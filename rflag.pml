// basic one instance of Paxos (aka Synod)
//
// * Derived from the "Model Checking Paxos in Spin" paper
// * by Giorgio Delzanno, Michele Tatarek, and  Riccardo Traverso.
// * https://arxiv.org/pdf/1408.5962
//
// That work was Copyright(C) 2014 by these authors, and
// licensed under the Creative Commons Attribution License (CC-BY).
//
// * ...and then heavily altered, updated, and fixed
// * to the point where it is only distantly similar/might not
// * even be recognizable from the originally presented form.
//
// This version: Copyright(C) 2025 by Jason E. Aten, Ph.D.
// License (kept the same): Creative Commons Attribution License (CC-BY).

/* simple paxos, one round of Synod (herein, this is NOT multi-paxos):
   Proposer -> Prepare -> Acceptors
   Acceptors -> Promise -> Proposer
   Proposer -> Accept -> Acceptors
   Acceptors -> Learn -> Learners
*/

#define ACCEPTORS 3
#define PROPOSERS 3   // 2 sec
//define PROPOSERS 5  // 181 sec

// Normal (should not be faulty).
#define MAJORITY (ACCEPTORS / 2 + 1)
//
// Try to get a fault detected:
//
// MAJORITY==1 should be faulty if PROPOSERS and ACCEPTORS >= 2
//define MAJORITY 1

#define MAX (ACCEPTORS*PROPOSERS)

typedef msgPromise{
  byte  promised;    // promised (reject lower number proposals)
  short acceptedNum; // previously accepted round number
  short acceptedVal; // previously accepted value
}

chan phase1aPrepare = [MAX] of {byte, byte}; // to acceptor i, ballot.
chan phase1bPromise = [MAX] of {msgPromise}; 
chan phase2aAcceptPlease = [MAX] of {byte, byte, short};
chan phase2bLearn = [MAX] of {short, short, short}; // learning

//
// Section 6 of paper, optimized version
//

// proposer i subroutine in phase 2. pr is a temp var to read promise messages.
inline accumHighest(i, pr, count, highestAcceptedRound, highestAcceptedValue, curBallot) {
 d_step{
  printf("i = %d, len(phase1bPromise) = %d; len(phase1aPrepare) = %d\n", i, len(phase1bPromise), len(phase1aPrepare));
  
  do
   :: i < len(phase1bPromise) ->    // can we move to phase 2, sending acceptPlease?
     phase1bPromise ? pr; phase1bPromise ! pr; // read+replace minimizes state changes
     if
       :: pr.promised == curBallot ->
          count++;
          if
            :: pr.acceptedNum > highestAcceptedRound ->
                   highestAcceptedRound = pr.acceptedNum;
                   highestAcceptedValue = pr.acceptedVal;
            :: else
          fi;
       //:: pr.promised > curBallot -> // must abort the round, right? + try higher ballot
       //  assert(false); // does this happen? yes. acceptors should be rejecting too
       :: else
     fi;
     i++;
  :: else ->
     pr.acceptedNum =0; pr.acceptedVal =0; pr.promised =0; i=0;
     break;
 od;
 }
}

// broadcast phase2aAcceptPlease to the acceptors when
// the phase 1 majority is detected.
//
inline checkPrepQuorum(count, highestAcceptedRound, highestAcceptedValue,
                       myval, curBallot, applyVal) {
  if
    :: count >=MAJORITY ->
         applyVal =(highestAcceptedRound < 0 -> myval : highestAcceptedValue); 
         // manually inlined bcastPhase2aAcceptPlease(curBallot, applyVal)...
         int k = 1; 
         do
           ::(k <= ACCEPTORS) ->
              printf("k = %d in bcastPhase2aAcceptPlease inline, ACCEPTORs=%d\n", k, ACCEPTORS);
              phase2aAcceptPlease !! k, curBallot, applyVal;
              k++;
           ::else -> break;
         od
         break;
    :: else
  fi;
}

// a proposer i does phase 2. pr is a promise message.
inline proposerPhase2(i, pr, count, highestAcceptedRound, highestAcceptedValue, myval,curBallot, aux) {
  atomic {
    accumHighest(i, pr, count, highestAcceptedRound, highestAcceptedValue, curBallot);
    checkPrepQuorum(count, highestAcceptedRound, highestAcceptedValue, myval, curBallot, aux); 
    highestAcceptedValue= -1; highestAcceptedRound = -1; count = 0; aux = 0; 
  }
}

proctype proposer(short curBallot; short myval) {
  short aux, highestAcceptedRound = -1, highestAcceptedValue = -1;
  short rnd;
  short acceptedNum, acceptedVal;
  byte count =0, i = 0;
  // pr is a temp variable to read the phase1 promise messages we have received.
  msgPromise pr;
  d_step {
  
    // broadcast phase1aPrepare(curBallot);

    byte j = 1;
    do
     ::(j <= ACCEPTORS) -> 
        phase1aPrepare !! j, curBallot;
        printf("sent on phase1aPrepare j = %d, curBallot = %d\n", j, curBallot);
        j++;
     :: else -> break; // we have prepare quorum.
    od
    // end of manually unrolled broadcastPhase1aPrepare(curBallot);
  } // end of d_step
  
  // begin phase 2, after prepare quorum achieved.
  end: do
        :: proposerPhase2(i, pr, count, highestAcceptedRound, highestAcceptedValue, myval, curBallot, aux);
       od
}


proctype acceptor(int id) {

  printf("top of acceptor, id = %d; len(phase1aPrepare) = %d\n", id, len(phase1aPrepare));
  
  short promisedN = -1; // max ballot seen.
  short acceptedNum = -1, acceptedVal = -1;
  short acceptThisVal;
  short rnd; // temp var to read round from the channels.
  
  // where is the promise to ignore lower ballots? is it promisedN?
  
  do
    :: d_step {
         // find the highest round so far. store it in promisedN.
         phase1aPrepare ?? <eval(id), rnd> ->
         printf("acceptor id = %d sees phase1aPrepare len %d: rnd = %d; promisedN = %d\n", id, len(phase1aPrepare), rnd, promisedN); // len 4, 1, 1. should hold 1,1,2,2
         if
           ::(rnd > promisedN) -> promisedN = rnd;
              //printf("promisedN is now %d\n", promisedN);
           :: else
         fi;
         rnd = 0
       }
       // we have to send back on phase1bPromise
       phase1bPromise !! promisedN, acceptedNum, acceptedVal;
       //printf("phase1aPrepare ?? was run, and phase1bPromise ! too\n");

       // why keep running phase 1 once quorum is reached? to allow new rounds, we think
       
    :: d_step {
         phase2aAcceptPlease ?? eval(id), rnd, acceptThisVal ->
         if
           ::(rnd >= promisedN) -> // ballot in rnd is >= promised, so accept.
             promisedN = rnd;
             acceptedNum = rnd;
             acceptedVal = acceptThisVal;

             // this looks wrong. should be sending the rnd, not promisedN.
             //phase2bLearn !! id, promisedN, acceptThisVal;
             phase2bLearn !! id, rnd, acceptThisVal;
             printf("acceptor id = %d replied on phase2bLearn\n", id);
           :: else
         fi;
         rnd = 0; acceptThisVal = 0;
       }
       break;
  od
  printf("end of acceptor id = %d\n", id);
}


inline read_learn_chan_assert(id, rnd, lval, lastval, acceptCount, done) {
  d_step {
    phase2bLearn ?? id, rnd, lval ->
       printf("read_learn read from phase2bLearn: id = %d, rnd = %d, lval = %d\n", id, rnd, lval);
    if
      :: acceptCount[rnd -1] < MAJORITY ->
           acceptCount[rnd -1]++;
           printf("read_learn: id = %d, rnd = %d, %d < MAJ\n", id, rnd, acceptCount[rnd-1]);
      :: else
    fi;
    if
      :: acceptCount[rnd -1] >= MAJORITY ->
           printf("read_learn: id = %d, acceptCount = %d >= MAJ\n", id, acceptCount[rnd-1]);      
         if :: (lastval >= 0 && lastval != lval) ->
                 printf("assert error: lastval: %d != lval: %d\n", lastval, lval);
                 assert(false); // equiv to assert(lastval < 0 || lastval == lval)
            :: (lastval == -1) -> lastval = lval; // free to chose it.
            :: else
         fi
         // I don't think we should do this; we want to keep checking
         // safety on past the first value that we learn...
         // done = true;  // Exit after learning a value
      :: else
    fi;
    id = 0; rnd = 0; lval = 0;
  }
}

// Active learner process that checks for safety:
// that only a single consistent value is chosen.
// The asserts are inside read_learn_chan_assert().
//
active proctype learn_and_assert_safety() {

  short lastval = -1, id, rnd, learnedValue;

  // per round, is this enough if we have conflicts+restarts?
  byte acceptCount[PROPOSERS]; 
  bool done = false;
  end:  do
          :: read_learn_chan_assert(id, rnd, learnedValue, lastval, acceptCount, done);
          :: done -> break;
        od
  printf("learn_and_assert_safety is done.\n");
}

init {
  atomic{  
    int j = 1;
    for (j : 1 .. PROPOSERS) {
      run proposer(j, j);
    }

    int k = 1;
    for (k : 1 .. ACCEPTORS) {
      run acceptor(k);
    }
  };
}
