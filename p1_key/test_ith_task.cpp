#include <iostream>
#include <map>
#include <queue>
#include <string>
#include <algorithm>
#include <bitset>
#include <chrono>
#include <cmath>
#include <climits>
#include <cinttypes>
#include "../custom_types/ts.h"
#include "../custom_types/state.h"
#include "../custom_types/my_types.h"
#include "../generate_successors.h"
#include "../algorithm_move.h"
#include "../get_map_binary_keys.h"
#include "../pruning_constraints.h"
#include <unordered_set>
#include <mutex>
#include <thread>
#include <condition_variable>
#include <set>

using namespace std;
using namespace std::chrono;

namespace NS_itasks
{

    // Class that represents a simple thread pool
    class ThreadPool
    {
    public:
        // // Constructor to creates a thread pool with given
        // number of threads
        ThreadPool(size_t num_threads = thread::hardware_concurrency())
        {

            // Creating worker threads
            for (size_t i = 0; i < num_threads; ++i)
            {
                threads_.emplace_back([this]
                                      {
                    while (true) {
                        function<void()> task;
                        // The reason for putting the below code
                        // here is to unlock the queue before
                        // executing the task so that other
                        // threads can perform enqueue tasks
                        {
                            // Locking the queue so that data
                            // can be shared safely
                            unique_lock<mutex> lock(
                                    queue_mutex_);

                            // Waiting until there is a task to
                            // execute or the pool is stopped
                            cv_.wait(lock, [this] {
                                return !tasks_.empty() || stop_;
                            });

                            // exit the thread in case the pool
                            // is stopped and there are no tasks
                            if (stop_ && tasks_.empty()) {
                                return;
                            }

                            // Get the next task from the queue
                            task = std::move(tasks_.front());
                            tasks_.pop();
                        }

                        task();
                    } });
            }
        }

        // Destructor to stop the thread pool
        ~ThreadPool()
        {
            {
                // Lock the queue to update the stop flag safely
                unique_lock<mutex> lock(queue_mutex_);
                stop_ = true;
            }

            // Notify all threads
            cv_.notify_all();

            // Joining all worker threads to ensure they have
            // completed their tasks
            for (auto &thread : threads_)
            {
                thread.join();
            }
        }

        // Enqueue task for execution by the thread pool
        void enqueue(function<void()> task)
        {
            {
                unique_lock<std::mutex> lock(queue_mutex_);
                tasks_.emplace(std::move(task));
            }
            cv_.notify_one();
        }

    private:
        // Vector to store worker threads
        vector<thread> threads_;

        // Queue of tasks
        queue<function<void()>> tasks_;

        // Mutex to synchronize access to shared data
        mutex queue_mutex_;

        // Condition variable to signal changes in the state of
        // the tasks queue
        condition_variable cv_;

        // Flag to indicate whether the thread pool should stop
        // or not
        bool stop_ = false;
    };

    // Main data structures
    TS ts; // the task system being analyzed
    uint8_t m;
    unsigned long int visitedStatesNum = 0;
    unsigned long int visitedStatesNum_withTauKpending = 0;
    unsigned long int savedStatesNum = 0;
    unsigned long int savedStatesNum_tauKpending = 0;
    bool verbose = false;
    mutex print_mut;

    double dominatedCount = 0;
    double t_insertIntoMap = 0;
    double t_searchForDominatingState = 0;
    unsigned long int t_searchForDominatedState = 0;
    unsigned long int t_SuccessorsGeneration = 0;
    unsigned long int t_algorithmMove = 0;
    unsigned long int t_adversaryPruning = 0;
    unsigned long int t0 = 0;

    template <typename Key, typename Value>
    pair<Value &, bool> map_get_or_insert(std::map<Key, Value> &tree, const Key &key)
    {
        auto res = tree.try_emplace(key, Value());
        return {res.first->second, res.second};
    }

    template <typename Key>
    class Node1
    {
    public:
        Node1() = default;

        unordered_set<unsigned int> ids;
        map<Key, Node1> child;
    };

    class SafeCounter
    {
    private:
        mutex m;
        unsigned short value;
        unsigned int last_changed;

    public:
        SafeCounter() : value(0), last_changed(0) {}

        SafeCounter(const SafeCounter &other)
        {
            value = other.value;
            last_changed = other.last_changed;
        };

        SafeCounter(SafeCounter &&) = default;

        bool incr(unsigned int cur)
        {
            if (cur == last_changed)
            {
                value++;
                return true;
            }
            if (cur < last_changed)
            {
                return false;
            }
            value = 1;
            last_changed = cur;
            return true;
        }

        unsigned short get_value(unsigned int cur)
        {
            if (cur > last_changed)
            {
                return 0;
            }
            return value;
        }

        void lock()
        {
            m.lock();
        }

        void unlock()
        {
            m.unlock();
        }
    };

    class FastSearchMultiThread
    {
    public:
        explicit FastSearchMultiThread(int domain, unsigned short int task_space_id, unsigned int n)
        {
            this->n = n;
            this->task_space_id = task_space_id;
        }

        void insert(const unsigned short left, const unsigned short right, const state *state, unsigned int id, const unsigned short total, bool *stop,
                    unsigned short int *finished_num, mutex *mut, condition_variable *cv, mutex *cv_m)
        {
            if (verbose) {
                print_mut.lock();
                cout << "\t\t\tThread ID=" << this_thread::get_id() << ": Inserting in M_" << task_space_id << " started" << endl;
                print_mut.unlock();
            }
            auto left_tree = tree.try_emplace(left, map<unsigned short int, Node1<unsigned short int>>());
            auto right_tree = left_tree.first->second.try_emplace(right, Node1<unsigned short int>());
            for (int i = 0; i < state->tsLocal.n; ++i)
            {
                right_tree = right_tree.first->second.child.try_emplace(state->p[i] - state->c[i],
                                                                        Node1<unsigned short int>());
            }
            mut->lock();
            (*finished_num)++;
            if (*finished_num == total)
            {
                *stop = true;
            }
            {
                std::lock_guard<std::mutex> lk(*cv_m);
                cv->notify_one();
            }
            mut->unlock();
            right_tree.first->second.ids.insert(id);
            if (verbose) {
                print_mut.lock();
                cout << "\t\t\tThread ID=" << this_thread::get_id() << ": Insertion in M_" << task_space_id << " finished" << endl;
                print_mut.unlock();
            }
        }

        void
        query(const unsigned short ind, const state *state, const unsigned short total,
              vector<SafeCounter> *counter, bool *stop, unsigned int current_time, bool *res,
              unsigned short int *finished_num, mutex *mut, condition_variable *cv, mutex *cv_m)
        {
            const unsigned short left = state->c[ind];
            const unsigned short right = state->p[ind];
            if (verbose) {
                print_mut.lock();
                cout << "\t\t\tThread ID=" << this_thread::get_id() << ": Examination in M_" << task_space_id << " started" << endl;
                print_mut.unlock();
            }

            bool was_updated = false;
            for (auto it = tree.lower_bound(left);
                 !(*stop) && it != tree.end() && it->first <= right; ++it)
            {
                for (auto it2 = it->second.begin();
                     !(*stop) && it2 != it->second.end() && it2->first <= right; ++it2)
                {
                    rec(it2->second, state, total, 0, counter, stop, res, current_time, was_updated);
                }
            }
            if (!was_updated) {
                *stop = true;
                if (verbose) {
                    print_mut.lock();
                    cout << "\t\t\tThread ID=" << this_thread::get_id() << ": task state in M_" << task_space_id << " is not dominated" << endl;
                    print_mut.unlock();
                }
            } else {
                if (verbose) {
                    print_mut.lock();
                    cout << "\t\t\tThread ID=" << this_thread::get_id() << ": task state in M_" << task_space_id << " is dominated" << endl;
                    print_mut.unlock();
                }
            }
            mut->lock();
            (*finished_num)++;
            if (*finished_num == total)
                *stop = true;
            {
                std::lock_guard<std::mutex> lk(*cv_m);
                cv->notify_one();
            }
            mut->unlock();
            if (verbose) {
                cout << "\t\t\tThread ID=" << this_thread::get_id() << ": Examination in M_" << task_space_id << " finished" << endl;
            }
        }

        void
        find_dominated(const unsigned short ind, const state *state, const unsigned short total,
              vector<SafeCounter> *counter, bool *stop, unsigned int current_time, vector<unsigned int> *res,
              unsigned short int *finished_num, mutex *mut, condition_variable *cv, mutex *cv_m) {
            const unsigned short left = state->c[ind];
            const unsigned short right = state->p[ind];
            if (verbose) {
                print_mut.lock();
                cout << "Thread ID=" << this_thread::get_id() << ": Searching dominated for task state(c="<< left << ", p=" << right << ") in task space " << task_space_id << endl;
                print_mut.unlock();
            }

            bool was_updated = false;
            for (auto it = tree.begin();
                 !(*stop) && it != tree.end() && it->first <= left; ++it)
            {
                for (auto it2 = it->second.end();
                     !(*stop) && it2 != it->second.begin() && it2->first >= right; --it2)
                {
                    if(it->first == left && it2->first == right) continue;
                    recDominated(it2->second, state, total, 0, counter, stop, res, current_time, was_updated);
                }
            }
            if (!was_updated) {
                *stop = true;
                if (verbose) {
                    print_mut.lock();
                    cout << "Thread ID=" << this_thread::get_id() << ": task state(c="<< left << ", p=" << right << ") in task space " << task_space_id << " is not dominating any yet!" << endl;
                    print_mut.unlock();
                }
            } else {
                if (verbose) {
                    print_mut.lock();
                    cout << "Thread ID=" << this_thread::get_id() << ": task state(c="<< left << ", p=" << right << ") in task space " << task_space_id << " is dominating some states!" << endl;
                    print_mut.unlock();
                }
            }
            mut->lock();
            (*finished_num)++;
            if (*finished_num == total) {
                *stop = true;
            }
            mut->unlock();
            {
                std::lock_guard<std::mutex> lk(*cv_m);
                cv->notify_one();
            }
        }

        void rec(const Node1<unsigned short int> &node, const state *state, const unsigned short total,
                 unsigned short lengthDepth,
                 vector<SafeCounter> *counter, bool *stop, bool *res, unsigned int current_time, bool &was_updated)
        {
            if (state->tsLocal.n > lengthDepth)
            {
                auto length = state->p[lengthDepth] - state->c[lengthDepth];
                for (auto iter = node.child.begin();
                     !(*stop) && iter != node.child.end() && iter->first <= length; iter++)
                {
                    rec(iter->second, state, total, lengthDepth + 1, counter, stop, res, current_time, was_updated);
                }
                return;
            }
            for (const unsigned int cur_id : node.ids)
            {
                if (*stop)
                    return;
                (*counter)[cur_id].lock();
                auto was_updated_now = (*counter)[cur_id].incr(current_time);
                if (was_updated_now)
                    was_updated = true;
                else
                {
                    if (verbose) {
                        print_mut.lock();
                        cout << "\t\t\tThread ID=" << this_thread::get_id() << ": Not found any dominating tasks from other mas in M_" << task_space_id << endl;
                        cout << "\t\t\tThread ID=" << this_thread::get_id() << ": Setting examination stop flag" << endl;
                        print_mut.unlock();
                    }
                    *stop = true;
                    return;
                }
                auto val = (*counter)[cur_id].get_value(current_time);
                (*counter)[cur_id].unlock();
                if (val == total)
                {
                    if (verbose) {
                        print_mut.lock();
                        cout << "\t\t\tThread ID=" << this_thread::get_id() << ": State " << cur_id << " occured to be dominating  in M_" << task_space_id << endl;
                        cout << "\t\t\tThread ID=" << this_thread::get_id() << ": Setting examination stop flag" << endl;
                        print_mut.unlock();
                    }
                    *res = true;
                    *stop = true;
                }
            }
        }

        void recDominated(const Node1<unsigned short int> &node, const state *state, const unsigned short total,
                 unsigned short lengthDepth,
                 vector<SafeCounter> *counter, bool *stop, vector<unsigned int> *res, unsigned int current_time, bool &was_updated)
        {
            if (state->tsLocal.n > lengthDepth)
            {
                auto length = state->p[lengthDepth] - state->c[lengthDepth];
                for (auto iter = node.child.end();
                     !(*stop) && iter != node.child.begin() && iter->first >= length; iter--)
                {
                    recDominated(iter->second, state, total, lengthDepth + 1, counter, stop, res, current_time, was_updated);
                }
                return;
            }
            for (const unsigned int cur_id : node.ids)
            {
                if (*stop)
                    return;
                (*counter)[cur_id].lock();
                auto was_updated_now = (*counter)[cur_id].incr(current_time);
                if (was_updated_now)
                    was_updated = true;
                else
                {
                    *stop = true;
                    return;
                }
                auto val = (*counter)[cur_id].get_value(current_time);
                (*counter)[cur_id].unlock();
                if (val == total)
                {
                    dominatedCount++;
                    res->push_back(cur_id);
                }
            }
        }

        void print(string prefix = "", bool has_next = false) {
            cout << prefix << (has_next ? "├──" : "└──" ) << "M" << task_space_id << endl;
            auto tree_prefix = prefix + (has_next ? "│  " : "   ");
            for (auto it = tree.begin(); it != tree.end(); ++it)
            {
                auto last = prev(tree.end());
                auto is_last = (it == last);
                cout << tree_prefix;
                cout << (is_last ? "└──" : "├──");
                cout << it->first << endl;
                auto this_prefix = tree_prefix + (is_last ? "   " : "│  ");
                for (auto it2 = it->second.begin(); it2 != it->second.end(); ++it2) {
                    set<unsigned int> all_ids;
                    get_all_ids(it2->second, all_ids, 0);
                    auto last_p = prev(it->second.end());
                    auto is_last_p = (it2 == last_p);
                    cout << this_prefix;
                    cout << (is_last_p ? "└──" : "├──");
                    cout << it2->first;
                    cout << "───{";
                    int i = 1;
                    for (auto id: all_ids) {
                        cout << id;
                        if (i != all_ids.size()) cout << ",";
                        i++;
                    }
                    cout << "}" << endl;
                }
            }
        }

    private:
        void get_all_ids(const Node1<unsigned short int> &node, set<unsigned int>& res, unsigned int depth = 0) {
            if (n > depth)
            {
                for (auto iter = node.child.begin(); iter != node.child.end(); iter++) {
                    get_all_ids(iter->second, res, depth + 1);
                }
                return;
            }
            for (auto id: node.ids) {
                res.insert(id);
            }
        }

        map<unsigned short int,
            map<unsigned short int, Node1<unsigned short int>>>
            tree;
        unsigned short int task_space_id;
        unsigned int n;
    };

    class Node
    {
    public:
        Node() = default;

        explicit Node(vector<FastSearchMultiThread> vec)
        {
            this->vec = std::move(vec);
        }

        vector<FastSearchMultiThread> vec;
        map<unsigned short int, Node> children;
    };

    class IFastMultidimSearch
    {
    public:
        virtual ~IFastMultidimSearch() {};
        virtual void insert(const state *new_state) = 0;
        virtual bool query(const state *state, bool presort = true) = 0;
        virtual unsigned long int size() const = 0;
        virtual unsigned long int pending_num() const = 0;
        virtual void print() = 0;
    };

    class FastMultidimSearchMultiThread : public IFastMultidimSearch
    {
    public:
        FastMultidimSearchMultiThread(int dim_num, int domain)
        {
            this->N = dim_num;
            pool = new ThreadPool(4);
            pool2 = new ThreadPool(4);
            dims.reserve(N);
            for (unsigned short int i = 0; i < N; ++i)
                dims.emplace_back(16, i, N);
            *finished_dominating_jobs = N;
            *finished_dominated_jobs = N;
        }

        virtual void insert(const state *new_state) override
        {
            if(verbose) {
                print_mut.lock();
                cout << "\t\tInserting state " << n << ":" << endl << "\t\t";
                for (size_t i = 0; i < N; ++i) {
                    cout << "(" << (const unsigned short) new_state->c[i] << ", "<< (const unsigned short) new_state->p[i] << ") ";
                }
                cout << endl;
                print_mut.unlock();
            }
            // Single threaded version
            for (size_t i = 0; i < N; ++i) {
                dims[i].insert(new_state->c[i], new_state->p[i], new_state, n, N, insertion_stop, finished_insertion_jobs, insertion_mut, cv_insertion, cv_m_insertion);
            }
            // Multi threaded version
            // *insertion_stop = false;
            // *finished_insertion_jobs = 0;
            // for (size_t i = 0; i < N; ++i)
            // {
            //     pool2->enqueue([this, i, new_state]
            //                   { dims[i].insert(new_state->c[i], new_state->p[i], new_state, n, N, insertion_stop, finished_insertion_jobs, insertion_mut, cv_insertion, cv_m_insertion); });
            // }

            // unique_lock<std::mutex> lk(*cv_m_insertion);
            // cv_insertion->wait(lk, [this]
            //                    { return *insertion_stop; });
            if (new_state->c[N - 1] > 0)
                pen++;
            n++;
            dominating_counter->emplace_back();
            dominated_counter->emplace_back();
            if(verbose) {
                print_mut.lock();
                cout << "\t\tInsertion of state " << n << " finished" << endl;
                print_mut.unlock();
            }
        }

        virtual bool query(const state *state, bool presort = true) override
        {
            dominating_query_n++;
            dominated_query_n++;
            vector<unsigned short int> sorted_indices{};
            vector<unsigned short int> lens{};
            sorted_indices.reserve(N);
            *dominating_res = false;
            if(verbose) {
                print_mut.lock();
                cout << "\t\tSearch for dominating state " << n << ":" << endl << "\t\t";
                for (size_t i = 0; i < N; ++i) {
                    cout << "(" << (const unsigned short) state->c[i] << ", "<< (const unsigned short) state->p[i] << ") ";
                }
                cout << endl;
                print_mut.unlock();
            }

            for (int i = 0; i < N; i++)
            {
                sorted_indices.push_back(i);
                lens.push_back((unsigned short)(state->p[i] - state->c[i]));
            }

            if (presort)
            {
                print_mut.lock();
                if(verbose) {
                    cout << "\t\tSorting task states by increasing c_i - p_i" << endl;
                }
                std::sort(sorted_indices.begin(), sorted_indices.end(), [&state](auto left, auto right)
                          { return compare_tasks(state, left, right); });
                if(verbose) {
                    cout << "\t\tThe order of visiting M trees is following:";
                    for (auto id: sorted_indices) {
                        cout << " " << id;
                    }
                    cout << endl;
                }
                print_mut.unlock();
            }

            if (verbose) {
                cout << "\t\tWaiting till thread pool is ready" << endl;
            }
            while (true)
            {
                dominating_mut->lock();
                if (*finished_dominating_jobs == N)
                {
                    dominating_mut->unlock();
                    break;
                }
                dominating_mut->unlock();
            }

            *dominating_stop = false;
            *finished_dominating_jobs = 0;
            if (verbose) {
                cout << "\t\tThread pool is ready" << endl;
                cout << "\t\tStarting threads for " << n <<" state being dominated examination:" << endl;
            }
            for (auto ind : sorted_indices)
            {
                if (verbose) {
                    cout << "\t\t\tStarting thread for examination of " << ind << "th task state in M_" << ind << endl;
                }
                pool->enqueue([this, ind, state]
                              { dims[ind].query(ind, state, N, dominating_counter, dominating_stop, dominating_query_n, dominating_res, finished_dominating_jobs, dominating_mut, cv_dominating, cv_m_dominating); });
            }
            
            unique_lock<std::mutex> lk(*cv_m_dominating);
            if (verbose) {
                cout << "\t\tWaiting till stop flag is set" << endl;
            }
            cv_dominating->wait(lk, [this]
                     { return *dominating_stop; });

            
            // while (true)
            // {
            //     dominated_mut->lock();
            //     if (*finished_dominated_jobs == N)
            //     {
            //         dominated_mut->unlock();
            //         break;
            //     }
            //     dominated_mut->unlock();
            // }
            // *dominated_stop = false;
            // *finished_dominated_jobs = 0;
            // dominated_res->clear();
            // for (auto ind : sorted_indices)
            // {
            //     pool2->enqueue([this, ind, state]
            //                   { dims[ind].find_dominated(ind, state, N, dominated_counter, dominated_stop, dominated_query_n, dominated_res, finished_dominated_jobs, dominated_mut, cv_dominated, cv_m_dominated); });
            // }

            // unique_lock<std::mutex> lk2(*cv_m_dominated);
            // cv_dominated->wait(lk2, [this]
            //          { return *dominated_stop; });

            // if (verbose) {
            //     print_mut.lock();
            //     if (dominated_res->empty()) {
            //         cout << "State is not dominating!" << endl;
            //     } else {
            //         cout << "State is dominating for {";
            //         for (auto id: *dominated_res) {
            //             cout << id << ",";
            //         }
            //         cout << "}" << endl;
                    
            //     }
            //     cout << endl;
            //     print_mut.unlock();
            // }
            

            if(verbose) {
                print_mut.lock();
                if (*dominating_res) {
                    cout << "\tState is dominated!" << endl;
                } else {
                    cout << "\tState is not dominated!" << endl;
                }
                print_mut.unlock();
            }
            return *dominating_res;
        }

        [[nodiscard]] virtual unsigned long int size() const override
        {
            return n;
        }

        [[nodiscard]] virtual unsigned long int pending_num() const override
        {
            return pen;
        }

        void print() {
            cout << "└──M" << endl;
            for(int i = 0; i < dims.size(); i++){
                if (i == dims.size() - 1)
                    dims[i].print("   ", false);
                else
                    dims[i].print("   ", true);
            }
        }

        ~FastMultidimSearchMultiThread()
        {
            // Common
            delete pool;
            delete pool2;
            dims.clear();

            // Insertion
            delete cv_insertion;
            delete cv_m_insertion;
            delete insertion_stop;
            delete insertion_mut;
            delete finished_insertion_jobs;


            // Dominating
            dominating_counter->clear();
            delete cv_dominating;
            delete cv_m_dominating;
            delete dominating_counter;
            delete dominating_stop;
            delete dominating_res;
            delete dominating_mut;
            delete finished_dominating_jobs;

            // Dominated
            dominated_counter->clear();
            dominated_res->clear(); // Specific for dominated res
            delete cv_dominated;
            delete cv_m_dominated;
            delete dominated_counter;
            delete dominated_stop;
            delete dominated_res;
            delete dominated_mut;
            delete finished_dominated_jobs;
        }

    private:
        condition_variable *cv_insertion = new condition_variable();
        mutex *cv_m_insertion = new mutex();

        unsigned long int n = 0;
        unsigned long int pen = 0;
        unsigned short int N;

        vector<SafeCounter> *dominating_counter = new vector<SafeCounter>;
        bool *dominating_stop = new bool();
        mutex *dominating_mut = new mutex();
        unsigned short int *finished_dominating_jobs = new unsigned short int();
        bool *dominating_res = new bool();
        unsigned int dominating_query_n = 0;
        condition_variable *cv_dominating = new condition_variable();
        mutex *cv_m_dominating = new mutex();

        vector<SafeCounter> *dominated_counter = new vector<SafeCounter>;
        bool *dominated_stop = new bool();
        mutex *dominated_mut = new mutex();
        unsigned short int *finished_dominated_jobs = new unsigned short int();
        vector<unsigned int> *dominated_res = new vector<unsigned int>();
        unsigned int dominated_query_n = 0;
        condition_variable *cv_dominated = new condition_variable();
        mutex *cv_m_dominated = new mutex();

        ThreadPool *pool;
        ThreadPool *pool2;
        vector<FastSearchMultiThread> dims;
        bool *insertion_stop = new bool();
        unsigned short int *finished_insertion_jobs = new unsigned short int();
        mutex *insertion_mut = new mutex();

        static bool compare_tasks(const state *state, unsigned short int first, unsigned short int second)
        {
            unsigned short int len_first, len_second;
            len_first = state->p[first] - state->c[first];
            len_second = state->p[second] - state->c[second];
            return state->p[second] == 0 || ((len_first < len_second) && state->p[first] != 0);
        }
    };

    class FastSearchSingleThread
    {
    public:
        explicit FastSearchSingleThread(int domain) {}

        void insert(const unsigned short &left, const unsigned short &right, const state *state, unsigned int id)
        {
            auto left_tree = tree.try_emplace(left, map<unsigned short int, Node1<unsigned short int>>());
            auto right_tree = left_tree.first->second.try_emplace(right, Node1<unsigned short int>());
            for (int i = 0; i < state->tsLocal.n; ++i)
            {
                right_tree = right_tree.first->second.child.try_emplace(state->p[i] - state->c[i],
                                                                        Node1<unsigned short int>());
            }
            right_tree.first->second.ids.insert(id);
        }

        void
        query(const unsigned short ind, const state *state, const unsigned short total,
              vector<SafeCounter> &counter, bool &stop, unsigned int current_time, bool &res)
        {
            auto left = state->c[ind];
            auto right = state->p[ind];

            for (auto it = tree.lower_bound(left);
                 !stop && it != tree.end() && it->first <= right; ++it)
            {
                for (auto it2 = it->second.begin();
                     !stop && it2 != it->second.end() && it2->first <= right; ++it2)
                {
                    rec(it2->second, state, total, 0, counter, stop, res, current_time);
                }
            }
        }

        void rec(const Node1<unsigned short int> &node, const state *state, const unsigned short total,
                 unsigned short lengthDepth,
                 vector<SafeCounter> &counter, bool &stop, bool &res, unsigned int current_time)
        {
            if (state->tsLocal.n > lengthDepth)
            {
                auto length = state->p[lengthDepth] - state->c[lengthDepth];
                for (auto iter = node.child.begin();
                     !stop && iter != node.child.end() && iter->first <= length; iter++)
                {
                    rec(iter->second, state, total, lengthDepth + 1, counter, stop, res, current_time);
                }
            }
            for (const unsigned int cur_id : node.ids)
            {
                counter[cur_id].lock();
                counter[cur_id].incr(current_time);
                auto val = counter[cur_id].get_value(current_time);
                counter[cur_id].unlock();
                if (val == total)
                {
                    res = true;
                }
            }
        }

    private:
        map<unsigned short int,
            map<unsigned short int, Node1<unsigned short int>>>
            tree;
    };

    class FastMultidimSearchSingleThread : public IFastMultidimSearch
    {
    public:
        FastMultidimSearchSingleThread(int dim_num, int domain)
        {
            this->N = dim_num;
            dims.reserve(N);
            for (int i = 0; i < N; ++i)
                dims.emplace_back(16);
        }

        virtual void insert(const state *new_state) override
        {
            for (size_t i = 0; i < N; ++i)
            {
                dims[i].insert(new_state->c[i], new_state->p[i], new_state, n);
            }
            if (new_state->c[N - 1] > 0)
                pen++;
            n++;
            counter.emplace_back();
        }

        virtual bool query(const state *state, bool presort = true) override
        {
            query_n++;
            bool stop = false;
            res = false;
            vector<unsigned short int> sorted_indices{};
            vector<unsigned short int> lens{};
            sorted_indices.reserve(N);

            for (int i = 0; i < N; i++)
            {
                sorted_indices.push_back(i);
                lens.push_back((unsigned short)(state->p[i] - state->c[i]));
            }

            if (presort)
            {
                std::sort(sorted_indices.begin(), sorted_indices.end(), [&state](auto left, auto right)
                          { return compare_tasks(state, left, right); });
            }

            unsigned short i = 0;
            for (auto ind : sorted_indices)
            {
                i += 1;
                dims[ind].query(ind, state, i, counter, stop, query_n, res);
                if (!res)
                {
                    return false;
                }
                res = false;
                stop = false;
            }
            return true;
        }

        [[nodiscard]] unsigned long int size() const
        {
            return n;
        }

        [[nodiscard]] unsigned long int pending_num() const
        {
            return pen;
        }

        void print() {
            
        }

    private:
        unsigned int n = 0;
        unsigned int pen = 0;
        unsigned short int N;
        vector<SafeCounter> counter;
        //        ThreadPool pool = ThreadPool(1);
        vector<FastSearchSingleThread> dims;
        bool res;
        unsigned int query_n = 0;

        static bool compare_tasks(const state *state, unsigned short int first, unsigned short int second)
        {
            unsigned short int len_first, len_second;
            len_first = state->p[first] - state->c[first];
            len_second = state->p[second] - state->c[second];
            return state->p[first] != 0 && (len_first > len_second || (len_first == len_second && first < second));
        }
    };

    void get_states_num(IFastMultidimSearch *generated, unsigned long int &statesNum,
                        unsigned long int &statesNum_tauKpending)
    {
        statesNum = (*generated).size();
        statesNum_tauKpending = (*generated).pending_num();
    }

    bool find_dominating_state(const state *state, IFastMultidimSearch *visitedStates)
    {
        return (*visitedStates).query(state, true);
    }

    void add_state_to_map(const state *stateToAdd, IFastMultidimSearch *visitedStates)
    {
        (*visitedStates).insert(stateToAdd);
    }

    /**
     *
     * @return true - if the state is "unique" AND false if the state is dominated
     */
    bool update_map(const state *currentState, IFastMultidimSearch *visitedStates, const bool removeStates)
    {
        if (verbose) cout << "Examining alg state for map update:\n";
        // Check if some state in map dominates state s
        auto dominatingSearchStart = high_resolution_clock::now();
        if (verbose) cout << "\tSearch for dominating state:" << endl;
        if (find_dominating_state(currentState, visitedStates))
        {
            if (verbose) cout << "No map update because dominating state is found\n";
            t_searchForDominatingState += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - dominatingSearchStart).count();
            return false;
        }

        t_searchForDominatingState += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - dominatingSearchStart).count();

        // t0 = clock();
        // // No state in map dominates state s
        // if (removeStates) remove_dominated_states(s, visitedStates);
        // t_searchForDominatedState += clock() - t0;

        // State is not dominayed -> add to map to try dominate other states
        auto insertionStart = high_resolution_clock::now();
        add_state_to_map(currentState, visitedStates);
        t_insertIntoMap += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - insertionStart).count();
        if (verbose) {
            cout << "Map updated successfully" << endl;
            cout << "Updated map:" << endl;
            visitedStates->print();
        }
        return true;
    }

    bool populate(const unsigned short m_, const unsigned short n_, const TS &ts_, const bool removeStates)
    {

        ts = ts_;
        m = m_;

        savedStatesNum = 0;
        savedStatesNum_tauKpending = 0;
        visitedStatesNum = 0;
        visitedStatesNum_withTauKpending = 0;

        double total = 0;
        auto initializationStart = high_resolution_clock::now();
        auto generated = new FastMultidimSearchMultiThread(n_, TS::MAXN);
        double initializationTime = duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - initializationStart).count();

        state initial_state(ts);
        priority_queue<state> q;
        q.push(initial_state);

        state *s = new state(ts);
        bool schedulable = true;

        vector<state> *successors = new vector<state>(pow(2.0, ts.n), state(ts));
        unsigned short successorsNum;

        int ff = 0;

        while (!q.empty())
        {
            *s = q.top();
            q.pop();
            if (verbose) {
                cout << "Currently examined state:\n";
                s->print();
            }


            generate_successors(ts, *s, m, successors, successorsNum);

            // Analyse generated successors;
            // discard those successors which have been visited at previous iterations
            for (unsigned int successorItr = 0; successorItr < successorsNum; successorItr++)
            {
                *s = (*successors)[successorItr];
                if (verbose) {
                    cout << "Analyzing successor:\n";
                    s->print();
                }

                visitedStatesNum++;
                if ((*s).c[ts.n - 1] > 0)
                    visitedStatesNum_withTauKpending++;

                // UNCOMMENT HERE!!!
                if (!condition_for_releases_of_hp_jobs(*s))
                    continue;
                if (!condition_necessary_unsched(*s, m))
                    continue;

                int8_t algMove_ExitCode = algorithm_move(*s, ts.n, m, verbose);
                if (verbose) {
                    cout << "Updated analyzed successor:\n";
                    s->print();
                }

                if (algMove_ExitCode == -1)
                {
                    // deadline miss
                    schedulable = false;
                    break;
                }
                else if (algMove_ExitCode == 0)
                {
                    visitedStatesNum++;
                    if ((*s).c[ts.n - 1] > 0)
                        visitedStatesNum_withTauKpending++;

                    s->updateSumCs();
                    if (s->sumCs > 0)
                    {
                        s->updateSumSlacks();
                        s->updateLockedJobsNum();
                        s->updatePendJobsNum();
                        ff++;
                        if (update_map(s, generated, removeStates))
                            q.push(*s);
                    }
                }
                else
                {
                    // state is discarded
                }
            } // successors have been handled
            if (!schedulable)
                break;
        } // next iterations of while loop
        
        get_states_num(generated, savedStatesNum, savedStatesNum_tauKpending);

        // Clean memory
        auto cleanMemoryStart = high_resolution_clock::now();
        priority_queue<state> qEmpty;
        swap(q, qEmpty);
        delete generated;
        delete s;
        double cleanMemoryTime = duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - cleanMemoryStart).count();

        total = initializationTime + t_insertIntoMap + t_searchForDominatingState + cleanMemoryTime;
        cout << endl;
        cout << "Time analysis:" << endl;
        cout << "Total time:\t\t\t" << total * 1e-9 << "sec" << endl;
        cout << "Initialization:\t\t\t" << initializationTime / total * 100 << "%" << endl;
        cout << "Dominating search:\t\t" << t_searchForDominatingState / total * 100 << "%" << endl;
        cout << "Insertion:\t\t\t" << t_insertIntoMap / total * 100 << "%" << endl;
        cout << "Cleaning memory:\t\t\t" << cleanMemoryTime / total * 100 << "%" << endl;
        cout << "Dominated states count " << dominatedCount << endl;

        if (verbose)
        {
            cout << endl
                 << "P1 version: " << endl;
            cout << "Saved states:\t\t" << savedStatesNum << endl;
            if (savedStatesNum > 0)
                cout << "Saved states with tau_" << n_ << " pending: " << savedStatesNum_tauKpending << "  ( " << (float)((int)(savedStatesNum_tauKpending * 10000 / savedStatesNum)) / 100 << " %)" << endl;
            cout << "Visited states:\t\t" << visitedStatesNum << endl;
            cout << "Visited states with tau_" << n_ << " pending: " << visitedStatesNum_withTauKpending << "  ( " << (float)((int)(visitedStatesNum_withTauKpending * 10000 / visitedStatesNum)) / 100 << " %)" << endl
                 << endl;
        }

        return schedulable;
    }
} // end of namespace NS_itasks

bool test_ith_task(const bool verbose_, const uint8_t m_, const uint8_t n_, const TS &ts_, const bool removeStates_, unsigned long int &savedStatesNum_, unsigned long int &visitedStatesNum_)
{

    NS_itasks::verbose = verbose_;

    bool schedulable = NS_itasks::populate(m_, n_, ts_, removeStates_);
    savedStatesNum_ = NS_itasks::savedStatesNum;
    visitedStatesNum_ = NS_itasks::visitedStatesNum;

    return schedulable;
}
