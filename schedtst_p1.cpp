#include <iostream>
#include <string>
#include <fstream>
#include <chrono>
#include "custom_types/ts.h"
#include "p1_key/test_2d_task.h"
#include "p1_key/test_2d_task.h"
#include "p1_key/test_3d_task.h"
#include "p1_key/test_4th_task.h"
#include "p1_key/test_5th_task.h"
#include "p1_key/test_6th_task.h"
#include "p1_key/test_7th_task.h"
#include "p1_key/test_8th_task.h"
#include "p1_key/test_9th_task.h"
#include "p1_key/test_ith_task.h"
/*
#include "p1_key/test_10th_task.h"
#include "p1_key/test_11th_task.h"
#include "p1_key/test_12th_task.h"
#include "p1_key/test_13th_task.h"
#include "p1_key/test_14th_task.h"*/
#include <cinttypes>


using namespace std;
using namespace std::chrono;

ofstream fileResults;

// 6 Tasks example:
// 2 6 1 1 10 9 17 27 55 1 57 1 59 26 60 0 0

// 7 Tasks example:
// 2 7 1 6 10 8 14 1 21 1 23 1 23 1 33 1 10 0 0

// 8 Tasks example:
// 2 8 1 6 10 7 15 1 17 1 17 7 24 1 25 1 39 2 40 0 0

// 9 Tasks example:
// 2 9 1 6 10 7 15 1 17 1 17 7 24 1 25 1 39 2 40 1 40 0 0 - Exceeded timeout of 5 mins

// TODO:
// [V] Add print for initialization
// [V] Add info about thread pools capacity
// [V] To merge thread pool avaiability messages and add wating time print (i. e. "Thread pool is ready in ...ms")
// [V] Replace "Starting threads for 1 state.." with Dominating state search in threads:
// [V] Replace "1th task state" with "(2, 6) task state" 
// [V] Make outputs consistent in terms of M_1 (remove underscore)
// [V] Add message about setting stop flag where it is missing
// [V] Keep only 4 last digits of each thread in outputs.
// [V] Remove all the race issues in output
// [V] Shorten insertion messages for each thread, keep only info about insertion finish and time consumed (i. e. "Thread[1234]: Inserted (5, 6) in M0 in 5ms")
// [V] Fix message about end of insertion. Wrong id now.
// [-] Make less messages about search in task space. Print only one message about which task is processed and time (Discuss)
// [-]To discuss the printing the dominating state when found for ensuring algorithm correctness

int main(int argc, char* argv[]) {
    
    TS tsOriginal, ts;

    unsigned short m;
    cerr << "Number of processors?" << endl;
    cin >> m;
    
    unsigned short n;
    cerr << "Number of tasks?" << endl;
    cin >> n;
    
    bool implicitDeadlines = false;
    cerr << "Tasks have implicit deadlines? (1 - yes, 0 - no)" << endl;
    cin >> implicitDeadlines;
    
    tsOriginal.n = n;
    unsigned short C, D, P;
    for (unsigned short i = 0; i < n; i++) {
        cerr << "C[" << i << "]?" << endl;
        cin >> C;
        
        if (!implicitDeadlines) {
            cerr << "D[" << i << "]?" << endl;
            cin >> D;
        }
        
        cerr << "P[" << i << "]?" << endl;
        cin >> P;
        if (!implicitDeadlines) tsOriginal.setTask(i, C, D, P);
        else tsOriginal.setTask(i, C, P, P);
    }
    
    bool removeDominatedStatesFromMap = 0; // default setting
    cerr << "Dynamically optimize memory usage? (to remove states from memory at runtime):" << endl;
    cerr << "0 - no (recommended)" << endl;
    cerr << "1 - yes (might increase execution time)" << endl;
    cin >> removeDominatedStatesFromMap;
    
    bool verbose = 0;
    cerr << "Verbose? (0 - no, 1 -yes)" << endl;
    cin >> verbose;

    
    for (int i = 0; i < m; i++) ts.setTask(i, tsOriginal.C[i], tsOriginal.D[i], tsOriginal.P[i]);
    
    unsigned long int savedStatesNum = 0;
    unsigned long int visitedStatesNum = 0;
    unsigned long int savedStatesNumIncr = 0;
    unsigned long int visitedStatesNumIncr = 0;

    unsigned long int newSavedStatesNum = 0;
    unsigned long int newVisitedStatesNum = 0;
    unsigned long int newSavedStatesNumIncr = 0;
    unsigned long int newVisitedStatesNumIncr = 0;
    
    bool sched = true;
    bool newSched = true;
    
    unsigned long int t0;
    unsigned long int tExecution_p1;
    double total = 0;
    double newTotal = 0;
    unsigned long int tExecutionTotal_p1 = 0;
    auto start = high_resolution_clock::now();
    auto newStart = high_resolution_clock::now();
    
    for (uint8_t N = m + 1; N <= tsOriginal.n; N++) {
        ts.n = N;
        ts.setTask(N-1, tsOriginal.C[N-1], tsOriginal.D[N-1], tsOriginal.P[N-1]);

        if (verbose) {
            cout << endl << "===================" << endl;
            cout << "Checking task " << (int)ts.n << endl;
        }

        switch (N) {
            case 2:
                start = high_resolution_clock::now();
                sched = test_2d_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 2, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;
                
            case 3:
                start = high_resolution_clock::now();
                sched = test_3d_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 3, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;
                
            case 4:
                start = high_resolution_clock::now();
                sched = test_4th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 4, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;
                
            case 5:
                start = high_resolution_clock::now();
                sched = test_5th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 5, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;
                
            case 6:
                start = high_resolution_clock::now();
                sched = test_6th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 6, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;

            case 7:
                start = high_resolution_clock::now();
                sched = test_7th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 7, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;

            case 8:
                start = high_resolution_clock::now();
                sched = test_8th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 8, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;

            case 9:
                start = high_resolution_clock::now();
                sched = test_9th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 9, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;
            /*
            case 10:
                auto start = high_resolution_clock::now();
                sched = test_10th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 10, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;

            case 11:
                auto start = high_resolution_clock::now();
                sched = test_11th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 11, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;

            case 12:
                auto start = high_resolution_clock::now();
                sched = test_12th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 12, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;

            case 13:
                auto start = high_resolution_clock::now();
                sched = test_13th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 13, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;

            case 14:
                auto start = high_resolution_clock::now();
                sched = test_14th_task(verbose, m, ts, removeDominatedStatesFromMap, savedStatesNumIncr, visitedStatesNumIncr);
                total += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - start).count();
                savedStatesNum += savedStatesNumIncr; visitedStatesNum += visitedStatesNumIncr;

                newStart = high_resolution_clock::now();
                newSched = test_ith_task(verbose, m, 14, ts, removeDominatedStatesFromMap, newSavedStatesNumIncr, newVisitedStatesNumIncr);
                newTotal += duration_cast<chrono::nanoseconds>(high_resolution_clock::now() - newStart).count();
                newSavedStatesNum += newSavedStatesNumIncr; newVisitedStatesNum += newVisitedStatesNumIncr;
                break;*/

                
            default: cout << "No function defined to test " << N << " tasks!" << endl;
        }

        if (sched != newSched) {
            cout << "New algo works wrong!";
        }

        if (!sched || !newSched) break;
    }


    const char* fileName = (argv[2*(tsOriginal.n)+5]);

    fileResults.open(fileName, ios::app);
    fileResults << "\t" << sched << "\t" << tExecutionTotal_p1 << "\t" << savedStatesNum;
    fileResults.close();
    
    cout << "Sporadic burm2018 p1:\t\t" << (total* 1e-6) << " sec,  \t / " << savedStatesNum << " saved states" << "  \t / " << visitedStatesNum << " visited states" << endl;
    cout << "New algo p1:\t\t" << (newTotal* 1e-9) << " sec,  \t / " << newSavedStatesNum << " saved states" << "  \t / " << newVisitedStatesNum << " visited states";
    
    if (sched) cout << "  \t / SCHED" << endl;
    else cout << "  \t / UNSCHED" << endl;

    return sched;
}
