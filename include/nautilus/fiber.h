/* 
 * This file is part of the Nautilus AeroKernel developed
 * by the Hobbes and V3VEE Projects with funding from the 
 * United States National  Science Foundation and the Department of Energy.  
 *
 * The V3VEE Project is a joint project between Northwestern University
 * and the University of New Mexico.  The Hobbes Project is a collaboration
 * led by Sandia National Laboratories that includes several national 
 * laboratories and universities. You can find out more at:
 * http://www.v3vee.org  and
 * http://xstack.sandia.gov/hobbes
 *
 * Copyright (c) 2019, Michael A. Cuevas <cuevas@u.northwestern.edu>
 * Copyright (c) 2019, Enrico Deiana <ead@u.northwestern.edu>
 * Copyright (c) 2019, Peter A. Dinda <pdinda@northwestern.edu>
 * Copyright (c) 2019, The V3VEE Project  <http://www.v3vee.org> 
 *                     The Hobbes Project <http://xstack.sandia.gov/hobbes>
 * All rights reserved.
 *
 * Authors: Michael A. Cuevas <cuevas@u.northwestern.edu>
 *          Enrico Deiana <ead@u.northwestern.edu>
 *          Peter A. Dinda <pdinda@northwestern.edu>
 *
 * This is free software.  You are permitted to use,
 * redistribute, and modify it as specified in the file "LICENSE.txt".
 */

#ifndef __FIBER_H__
#define __FIBER_H__

#ifdef __cplusplus
extern "C" {
#endif

#ifndef __ASSEMBLER__

#include <nautilus/spinlock.h>
#include <nautilus/intrinsics.h>

#include <nautilus/scheduler.h>
#include <nautilus/thread.h>

typedef uint64_t nk_stack_size_t;
typedef struct nk_thread nk_thread_t;
#define FIBER_RAND_CPU_FLAG -2
#define FIBER_CURR_CPU_FLAG -1
#define YIELD_TO_EARLY_RET 1

/* common thread stack sizes */
#define FSTACK_DEFAULT 0 // will be 4K
#define FSTACK_4KB 0x001000
#define FSTACK_1MB 0x100000
#define FSTACK_2MB 0x200000

/********** EXTERNAL INTERFACE **********/

typedef void (*nk_fiber_fun_t)(void *input, void **output);

typedef enum {  INIT,               // Being initialized
           READY,               // Ready to be run, on a wait queue
	       YIELD,           // in process of yielding
           WAIT,           // being removed from fiber queue
                               // probably due to having been put into a wait queue
	       EXIT,            // being removed from RT and non-RT run/arrival queues
                                   // will not return
           RUN             // currently running routine (not on a fiber queue)
             } nk_fiber_status;

typedef struct nk_fiber {
  uint64_t rsp;                /* +0  SHOULD NOT CHANGE POSITION */
  void *stack;                 /* +8  SHOULD NOT CHANGE POSITION */
  uint16_t fpu_state_offset;   /* +16 SHOULD NOT CHANGE POSITION */
  
  nk_stack_size_t stack_size;
    
  spinlock_t lock; /* allows us to lock the fiber */
  nk_fiber_status f_status;
  
  // TODO MAC: need to figure out screen/keyboard I/O
  struct nk_virtual_console *vc; // for printing
  int is_idle; // indicates whether this is the idle fiber

  struct list_head wait_queue; // wait queue for fibers waiting on this fiber
  struct list_head wait_node;
  int num_wait;             // number of fibers on this fiber's wait queue

  // List for keeping track of fiber's children
  struct list_head fiber_children;
  struct list_head child_node;
  int num_children;
  
  struct list_head sched_node; // sched queue node
  int curr_cpu;  // current cpu the fiber is on

  nk_fiber_fun_t fun; // routine the fiber will execute
  void *input;  // input for the fiber's routine
  void **output;  // output for the fiber's routine

  uint8_t is_done; //indicates whether the fiber is done (for reaping?)
} nk_fiber_t;

// Returns the fiber that is currently running
nk_fiber_t *nk_fiber_current();

// TODO MAC: Reformat to make function header span multiple lines
// Create a fiber but do not launch it
int nk_fiber_create(nk_fiber_fun_t fun,
                    void *input,
                    void **output,
                    nk_stack_size_t stack_size,
                    nk_fiber_t **fiber_output);

// TODO MAC: Have this take CPU instead of flag (-1 is any CPU, otherwise choose specific CPU)
// Launch a previously created fiber
int nk_fiber_run(nk_fiber_t *f, int target_cpu);

// Create and launch a fiber
int nk_fiber_start(nk_fiber_fun_t fun,
                   void *input,
                   void **output,
                   nk_stack_size_t stack_size,
                   int target_cpu,
                   nk_fiber_t **fiber_output);

// Default yield function, implemented on top of conditional yield
int nk_fiber_yield();

// Yield that allows choice of fiber to yield to
// Will yield to a random fiber if f_to is not available to yield to
int nk_fiber_yield_to(nk_fiber_t *f_to, int earlyRetFlag);

// Takes a fiber to yield to, a condition to yield on, and a function to check that condition
// returns 1 if the fiber does not yield
int nk_fiber_conditional_yield_to(nk_fiber_t *fib, uint8_t (*cond_function)(void *param), void *state);

// Takes a fiber, a condition to yield on, and a function to check that condition
// returns 1 if the fiber does not yield
int nk_fiber_conditional_yield(uint8_t (*cond_function)(void *param), void *state);

// returns a copy of the currently running fiber with a new FID
nk_fiber_t *nk_fiber_fork();

// Causes the currently running fiber to wait on the specified fiber 
int nk_fiber_join(nk_fiber_t *wait_on);

// Set virtual console
void nk_fiber_set_vc(struct nk_virtual_console *vc);

int nk_fiber_init();

int nk_fiber_init_ap();

void nk_fiber_startup();

/********** WRAPPER NK FIBER YIELD **********/

int wrapper_nk_fiber_yield();

void print_data();


#endif /* !__ASSEMBLER */


#define FIBER_SAVE_GPRS() \
    movq %rax, -8(%rsp); \
    movq %rbx, -16(%rsp); \
    movq %rcx, -24(%rsp); \
    movq %rdx, -32(%rsp); \
    movq %rsi, -40(%rsp); \
    movq %rdi, -48(%rsp); \
    movq %rbp, -56(%rsp); \
    movq %r8,  -64(%rsp); \
    movq %r9,  -72(%rsp); \
    movq %r10, -80(%rsp); \
    movq %r11, -88(%rsp); \
    movq %r12, -96(%rsp); \
    movq %r13, -104(%rsp); \
    movq %r14, -112(%rsp); \
    movq %r15, -120(%rsp); \
    subq $120, %rsp; 

#define FIBER_RESTORE_GPRS() \
    movq (%rsp), %r15; \
    movq 8(%rsp), %r14; \
    movq 16(%rsp), %r13; \
    movq 24(%rsp), %r12; \
    movq 32(%rsp), %r11; \
    movq 40(%rsp), %r10; \
    movq 48(%rsp), %r9; \
    movq 56(%rsp), %r8; \
    movq 64(%rsp), %rbp; \
    movq 72(%rsp), %rdi; \
    movq 80(%rsp), %rsi; \
    movq 88(%rsp), %rdx; \
    movq 96(%rsp), %rcx; \
    movq 104(%rsp), %rbx; \
    movq 112(%rsp), %rax; \
    addq $120, %rsp;

#define FIBER_RESTORE_GPRS_NOT_RAX() \
    movq (%rsp), %r15; \
    movq 8(%rsp), %r14; \
    movq 16(%rsp), %r13; \
    movq 24(%rsp), %r12; \
    movq 32(%rsp), %r11; \
    movq 40(%rsp), %r10; \
    movq 48(%rsp), %r9; \
    movq 56(%rsp), %r8; \
    movq 64(%rsp), %rbp; \
    movq 72(%rsp), %rdi; \
    movq 80(%rsp), %rsi; \
    movq 88(%rsp), %rdx; \
    movq 96(%rsp), %rcx; \
    movq 104(%rsp), %rbx; \
    addq $120, %rsp; 

/*
#define FIBER_SAVE_GPRS() \
    movq %rax, -8(%rsp); \
    movq %rbx, -16(%rsp); \
    movq %rcx, -24(%rsp); \
    movq %rdx, -32(%rsp); \
    movq %rsi, -40(%rsp); \
    movq %rdi, -48(%rsp); \
    movq %rbp, -56(%rsp); \
    movq %r8,  -64(%rsp); \
    movq %r9,  -72(%rsp); \
    movq %r10, -80(%rsp); \
    movq %r11, -88(%rsp); \
    movq %r12, -96(%rsp); \
    movq %r13, -104(%rsp); \
    movq %r14, -112(%rsp); \
    movq %r15, -120(%rsp); \
    movq %rsp, %rax; \
    subq $120, %rax; 

#define FIBER_RESTORE_GPRS() \
    movq (%rax), %r15; \
    movq 8(%rax), %r14; \
    movq 16(%rax), %r13; \
    movq 24(%rax), %r12; \
    movq 32(%rax), %r11; \
    movq 40(%rax), %r10; \
    movq 48(%rax), %r9; \
    movq 56(%rax), %r8; \
    movq 64(%rax), %rbp; \
    movq 72(%rax), %rdi; \
    movq 80(%rax), %rsi; \
    movq 88(%rax), %rdx; \
    movq 96(%rax), %rcx; \
    movq 104(%rax), %rbx; \
    movq %rax, %rsp; \
    movq 112(%rsp), %rax; \
    addq $120, %rsp;

#define FIBER_RESTORE_GPRS_NOT_RAX() \
    movq (%rsp), %r15; \
    movq 8(%rsp), %r14; \
    movq 16(%rsp), %r13; \
    movq 24(%rsp), %r12; \
    movq 32(%rsp), %r11; \
    movq 40(%rsp), %r10; \
    movq 48(%rsp), %r9; \
    movq 56(%rsp), %r8; \
    movq 64(%rsp), %rbp; \
    movq 72(%rsp), %rdi; \
    movq 80(%rsp), %rsi; \
    movq 88(%rsp), %rdx; \
    movq 96(%rsp), %rcx; \
    movq 104(%rsp), %rbx; \
    addq $120, %rsp; 
*/


#ifdef __cplusplus
}
#endif

#endif /* !__FIBER_H__ */
