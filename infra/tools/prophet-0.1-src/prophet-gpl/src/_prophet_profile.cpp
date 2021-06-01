// Copyright (C) 2016 Fan Long, Martin Rianrd and MIT CSAIL 
// Prophet
// 
// This file is part of Prophet.
// 
// Prophet is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
// 
// Prophet is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with Prophet.  If not, see <http://www.gnu.org/licenses/>.
#include "_prophet_profile.h"
#include <signal.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#include <pthread.h>

#define MAX_IDX 2048000

static unsigned long *M = 0;
static unsigned long long *C = 0;
static unsigned long long global_cnt;
static pthread_mutex_t global_mutex;

static void prof_writeback() {
    char buffer[1000];
    sigset_t full, oldset;
    sigfillset(&full);
    sigprocmask(SIG_BLOCK, &full, &oldset);
    pthread_mutex_lock(&global_mutex);
    sprintf(buffer, "/tmp/__run%u.log", getpid());
    FILE *f = fopen(buffer, "w");
    assert( f != NULL);
    /*size_t cnt = 0;
    for (size_t i = 0; i < MAX_IDX; i++)
        if (M[i]) cnt ++;*/
    //fprintf(f, "%lu\n", cnt);
    for (unsigned long i = 0; i < MAX_IDX; i++) {
        if (M[i]) {
            fprintf(f, "%lu\n", i);
            fprintf(f, "%lu %llu\n", M[i], global_cnt - C[i]);
        }
    }
    fclose(f);
    pthread_mutex_unlock(&global_mutex);
    sigprocmask(SIG_SETMASK, &oldset, &full);
/*    std::ostringstream sout;
    sout << "/tmp/__run" << getpid() << ".log";
    std::string na = sout.str();
    std::fstream fout(na.c_str(), std::fstream::out);
    assert(fout.is_open());
    for (TrackMapTy::iterator it = M.begin(); it != M.end(); ++it) {
        fout << it->first << "\n";
        fout << it->second << " " << global_cnt - C[it->first] << "\n";
    }
    fout.close();*/
}

static void prof_handler(int sig, siginfo_t *info, void *ucp) {
    prof_writeback();
//    if ((sig == SIGFPE) || (sig == SIGSEGV))
        SIG_DFL(sig);
}

void __prof_init() {
    //fprintf(stderr, "prof init!!! %d\n", getpid());
    pthread_mutex_init(&global_mutex, 0);
    M = (unsigned long*)malloc(MAX_IDX * sizeof(unsigned long));
    C = (unsigned long long*)malloc(MAX_IDX * sizeof(unsigned long long));
    memset(M, 0, sizeof(unsigned long) * MAX_IDX);
    memset(C, 0, sizeof(unsigned long long) * MAX_IDX);
    atexit(prof_writeback);
    global_cnt = 0;

    // Set our handler for SIGFPE.
    struct sigaction sa;
    sa.sa_sigaction = prof_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART | SA_SIGINFO;
    sigaction(SIGFPE, &sa, NULL);

    // Set our handler for SIGSEGV
    sa.sa_sigaction = prof_handler;
    sigemptyset (&sa.sa_mask);
    sa.sa_flags = SA_RESTART | SA_SIGINFO;
    sigaction(SIGSEGV, &sa, NULL);

    sa.sa_sigaction = prof_handler;
    sigemptyset (&sa.sa_mask);
    sa.sa_flags = SA_RESTART | SA_SIGINFO;
    sigaction(SIGKILL, &sa, NULL);

    sa.sa_sigaction = prof_handler;
    sigemptyset (&sa.sa_mask);
    sa.sa_flags = SA_RESTART | SA_SIGINFO;
    sigaction(SIGINT, &sa, NULL);

    sa.sa_sigaction = prof_handler;
    sigemptyset (&sa.sa_mask);
    sa.sa_flags = SA_RESTART | SA_SIGINFO;
    sigaction(SIGTERM, &sa, NULL);

    sa.sa_sigaction = prof_handler;
    sigemptyset (&sa.sa_mask);
    sa.sa_flags = SA_RESTART | SA_SIGINFO;
    sigaction(SIGABRT, &sa, NULL);
}

// This can be called anywhere, so it has to be simple,
// not including any complicated lib calls, like malloc,
// which will trigger deadlock in asynchronize I/O &
// multithread programs.
void __prof_track(unsigned long loc_idx) {
    // We have to unmask all signals
    /*sigset_t full, oldset;
    sigfillset(&full);
    sigprocmask(SIG_BLOCK, &full, &oldset);*/
    if (M == 0) __prof_init();
    //pthread_mutex_lock(&global_mutex);
    assert( loc_idx < MAX_IDX);
    /*assert( M != NULL);
    assert( C != NULL);*/
    M[loc_idx]++;
    C[loc_idx] = global_cnt;
    global_cnt ++;
    if ((global_cnt & ((1 << 25) -1)) == 0)
        prof_writeback();
    /*pthread_mutex_unlock(&global_mutex);
    sigprocmask(SIG_SETMASK, &oldset, &full);*/
}

void __prof_exit() {
    prof_writeback();
}

