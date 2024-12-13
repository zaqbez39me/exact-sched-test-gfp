#include <iostream>
#include <map>
#include <queue>
#include <string>
#include <algorithm>
#include <bitset>
#include <cmath>
#include <climits>
#include <cinttypes>
#include "../custom_types/ts.h"
#include "../custom_types/state.h"
#include "../custom_types/map_7_tasks.h"
#include "../generate_successors.h"
#include "../algorithm_move.h"
#include "../get_map_binary_keys.h"
#include "../pruning_constraints.h"
#include <unordered_set>
#include <mutex>
#include <thread>
#include <condition_variable>


using namespace std;

namespace NS_7tasks {

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

    unsigned long int t_insertIntoMap = 0;
    unsigned long int t_searchForDominatingState = 0;
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
        explicit FastSearchMultiThread(int domain, unsigned short int task_space_id) {
            this->task_space_id = task_space_id;
        }

        void insert(const unsigned short left, const unsigned short right, const state *state, unsigned int id)
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
              vector<SafeCounter> *counter, bool *stop, unsigned int current_time, bool *res,
              unsigned short int *finished_num, mutex *mut, condition_variable *cv, mutex *cv_m)
        {
            auto left = state->c[ind];
            auto right = state->p[ind];

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
            if (!was_updated)
                *stop = true;
            mut->lock();
            (*finished_num)++;
            if (*finished_num == total) *stop = true;
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
                else {
                    *stop = true;
                    return;
                }
                auto val = (*counter)[cur_id].get_value(current_time);
                (*counter)[cur_id].unlock();
                if (val == total)
                {
                    *res = true;
                    *stop = true;
                }
            }
        }

    private:
        map<unsigned short int,
            map<unsigned short int, Node1<unsigned short int>>>
            tree;
        unsigned short int task_space_id;
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
    };

    class FastMultidimSearchMultiThread : public IFastMultidimSearch
    {
    public:
        FastMultidimSearchMultiThread(int dim_num, int domain)
        {
            this->N = dim_num;
            pool = new ThreadPool(4);
            dims.reserve(N);
            for (unsigned short int i = 0; i < N; ++i)
                dims.emplace_back(16, i);
            *finished_jobs = N;
        }

        virtual void insert(const state *new_state) override
        {
            for (size_t i = 0; i < N; ++i) {
                dims[i].insert(new_state->c[i], new_state->p[i], new_state, n);
            }
            // for (size_t i = 0; i < N; ++i)
            // {
            //     pool->enqueue([this, i, new_state]
            //                   { dims[i].insert(new_state->c[i], new_state->p[i], new_state, n, finished_jobs, query_mut); });
            // }

            // // this_thread::sleep_for(std::chrono::milliseconds(1));
            // while (true) {
            //     this_thread::sleep_for(std::chrono::milliseconds(1));
            //     query_mut->lock();
            //     auto val = *finished_jobs;
            //     query_mut->unlock();
            //     if(val == N) break;
            // }
            // while (*finished_jobs != N)
            // {
            // }
            if (new_state->c[N - 1] > 0)
                pen++;
            n++;
            counter->emplace_back();
        }

        virtual bool query(const state *state, bool presort = true) override
        {
            query_n++;
            vector<unsigned short int> sorted_indices{};
            vector<unsigned short int> lens{};
            sorted_indices.reserve(N);
            *res = false;

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

            while(true) {
                query_mut->lock();
                if(*finished_jobs == N) {
                    query_mut->unlock();
                    break;
                }
                query_mut->unlock();
            }
            *stop = false;
            *finished_jobs = 0;
            for (auto ind : sorted_indices)
            {
                pool->enqueue([this, ind, state]
                              { dims[ind].query(ind, state, N, counter, stop, query_n, res, finished_jobs, query_mut, cv, cv_m); });
            }

            unique_lock<std::mutex> lk(*cv_m);
            cv->wait(lk, [this]{ return *stop; });
            return *res;
        }

        [[nodiscard]] virtual unsigned long int size() const override
        {
            return n;
        }

        [[nodiscard]] virtual unsigned long int pending_num() const override
        {
            return pen;
        }

    private:
        condition_variable *cv = new condition_variable();
        mutex *cv_m = new mutex();
        unsigned long int n = 0;
        unsigned long int pen = 0;
        unsigned short int N;
        vector<SafeCounter> *counter = new std::vector<SafeCounter>;
        ThreadPool *pool;
        vector<FastSearchMultiThread> dims;
        bool *stop = new bool();
        bool *res = new bool();
        unsigned short int *finished_jobs = new unsigned short int();
        mutex *query_mut = new mutex();
        unsigned int query_n = 0;

        static bool compare_tasks(const state *state, unsigned short int first, unsigned short int second)
        {
            unsigned short int len_first, len_second;
            len_first = state->p[first] - state->c[first];
            len_second = state->p[second] - state->c[second];
            return (len_first < len_second || (len_first == len_second && first < second)) && state->p[first] != 0;
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
            return (len_first < len_second || (len_first == len_second && first < second)) && state->p[first] != 0;
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

        // Check if some state in map dominates state s
        t0 = clock();

        if (find_dominating_state(currentState, visitedStates))
        {
            t_searchForDominatingState += clock() - t0;
            return false;
        }

        t_searchForDominatingState += clock() - t0;

        // t0 = clock();
        // // No state in map dominates state s
        // if (removeStates) remove_dominated_states(s, visitedStates);
        // t_searchForDominatedState += clock() - t0;

        // State is not dominayed -> add to map to try dominate other states
        t0 = clock();
        add_state_to_map(currentState, visitedStates);
        t_insertIntoMap += clock() - t0;

        return true;
    }
    
    
    bool populate(const unsigned short m_, const TS& ts_, const bool removeStates) {
        
        ts = ts_;
        m = m_;

        
        savedStatesNum = 0;
        savedStatesNum_tauKpending = 0;
        visitedStatesNum = 0;
        visitedStatesNum_withTauKpending = 0;
        auto generated = new FastMultidimSearchMultiThread(7, TS::MAXN);
        
        state initial_state(ts);
        priority_queue<state> q;
        q.push(initial_state);
        
        state *s = new state(ts);
        bool schedulable = true;
        
        vector<state>* successors = new vector<state>(pow(2.0, ts.n), state(ts));
        unsigned short successorsNum;

        int ff = 0;

        while (!q.empty()) {
            *s = q.top();
            q.pop();
            
            generate_successors(ts, *s, m, successors, successorsNum);
            
            // Analyse generated successors;
            // discard those successors which have been visited at previous iterations
            for (unsigned int successorItr = 0; successorItr < successorsNum; successorItr++) {
                *s = (*successors)[successorItr];
                
                visitedStatesNum++;
                if ((*s).c[ts.n-1] > 0) visitedStatesNum_withTauKpending++;
                
                if (!condition_for_releases_of_hp_jobs(*s)) continue;
                if (!condition_necessary_unsched(*s, m)) continue;
                
                int8_t algMove_ExitCode = algorithm_move(*s, ts.n, m, verbose);
                
                if (algMove_ExitCode == -1) {
                    // deadline miss
                    schedulable = false;
                    break;
                } else if (algMove_ExitCode == 0) {
                    visitedStatesNum++;
                    if ((*s).c[ts.n-1] > 0) visitedStatesNum_withTauKpending++;
                    
                    s->updateSumCs();
                    if (s->sumCs > 0) {
                        s->updateSumSlacks();
                        s->updateLockedJobsNum();
                        s->updatePendJobsNum();
                        ff++;
                        if (update_map(s, generated, removeStates))
                            q.push(*s);
                    }
                    
                } else {
                    // state is discarded
                }
            } // successors have been handled
            if (!schedulable) break;
        } // next iterations of while loop

        cout << "Checked " << ff << " times!" << endl;
        
        get_states_num(generated, savedStatesNum, savedStatesNum_tauKpending);
        
        // Clean memory
        priority_queue<state> qEmpty;
        swap(q, qEmpty);
        delete generated;
        
        
        if (verbose) {
            cout << endl << "P1 version: " << endl;
            cout << "Saved states:\t\t" << savedStatesNum << endl;
            if (savedStatesNum > 0) cout << "Saved states with tau_7 pending: " << savedStatesNum_tauKpending << "  ( " << (float)((int)(savedStatesNum_tauKpending*10000/savedStatesNum))/100 << " %)" << endl;
            cout << "Visited states:\t\t" << visitedStatesNum << endl;
            cout << "Visited states with tau_7 pending: " << visitedStatesNum_withTauKpending << "  ( " << (float)((int)(visitedStatesNum_withTauKpending*10000/visitedStatesNum))/100 << " %)" << endl << endl;
        }
        
        return schedulable;
    }
} // end of namespace NS_7tasks





bool test_7th_task(const bool verbose_, const uint8_t m_, const TS& ts_, const bool removeStates_, unsigned long int& savedStatesNum_, unsigned long int& visitedStatesNum_) {
    
    NS_7tasks::verbose = verbose_;
    
    bool schedulable = NS_7tasks::populate(m_, ts_, removeStates_);
    savedStatesNum_ = NS_7tasks::savedStatesNum;
    visitedStatesNum_ = NS_7tasks::visitedStatesNum;
    
    return schedulable;
}
