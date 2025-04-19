
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

/* simple paxos, one round of Synod (herein):
   Proposer -> Prepare -> Acceptors
   Acceptors -> Promise -> Proposer
   Proposer -> Accept -> Acceptors
   Acceptors -> Learn -> Learners

   MultiPaxos:
   Leader -> Prepare -> Acceptors  (once, at start)
   Acceptors -> Promise -> Leader
   Leader -> Accept -> Acceptors   (for each value)
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

chan phase1aPrepare = [MAX] of {byte, byte}; // to acceptor. recipient identity, ballot.
chan phase1bPromise = [MAX] of {msgPromise}; 
chan phase2aAcceptPlease = [MAX] of {byte, byte, short};
chan phase2bLearn = [MAX] of {short, short, short}; // learning

//
// Section 6 of paper, optimized versions of the above.
//

// a proposer subroutine in phase 2
inline occ(i, pr, count, highestAcceptedRound, highestAcceptedValue, curRound) {
 d_step{
  printf("i = %d, len(phase1bPromise) = %d; len(phase1aPrepare) = %d\n", i, len(phase1bPromise), len(phase1aPrepare));
  
  do
   :: i < len(phase1bPromise) ->    // can we move to phase 2, sending acceptPlease?
     phase1bPromise ? pr; phase1bPromise ! pr; // read+replace minimizes state changes
     if
       :: pr.promised == curRound ->
          count++;
          if
            :: pr.acceptedNum > highestAcceptedRound ->
               highestAcceptedRound = pr.acceptedNum; highestAcceptedValue = pr.acceptedVal;
            :: else
          fi;
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
                       myval, curRound, applyVal) {
  if
    :: count >=MAJORITY ->
         applyVal =(highestAcceptedRound < 0 -> myval : highestAcceptedValue); 
         // manually inlined bcastPhase2aAcceptPlease(curRound, applyVal)...
         int k = 1; 
         do
           ::(k <= ACCEPTORS) ->
              printf("k = %d in bcastPhase2aAcceptPlease inline, ACCEPTORs=%d\n", k, ACCEPTORS);
              phase2aAcceptPlease !! k, curRound, applyVal;
              k++;
           ::else -> break;
         od
         break;
    :: else
  fi;
}

// a proposer routine for phase 2
inline proposerPhase2(i, pr, count, highestAcceptedRound, highestAcceptedValue, myval,curRound, aux) {
  atomic {
    occ(i, pr, count, highestAcceptedRound, highestAcceptedValue, curRound);
    checkPrepQuorum(count, highestAcceptedRound, highestAcceptedValue, myval, curRound, aux); 
    highestAcceptedValue= -1; highestAcceptedRound = -1; count = 0; aux = 0; 
  }
}

proctype proposer_optimized(short curRound; short myval) {
  short aux, highestAcceptedRound = -1, highestAcceptedValue = -1;
  short rnd;
  short acceptedNum, acceptedVal;
  byte count =0, i = 0;
  msgPromise pr;
  d_step {
  
    // broadcast phase1aPrepare(curRound);

    byte j = 1;
    do
     ::(j <= ACCEPTORS) -> 
        phase1aPrepare !! j, curRound;
        printf("sent on phase1aPrepare j = %d, curRound = %d\n", j, curRound);
        j++;
     :: else -> break; // we have prepare quorum.
    od
    // end of manually unrolled broadcastPhase1aPrepare(curRound);
  } // end of d_step
  
  // begin phase 2, after prepare quorum achieved.
  end: do
        :: proposerPhase2(i, pr, count, highestAcceptedRound, highestAcceptedValue, myval, curRound, aux);
       od
}


proctype acceptor_optimized(int id) {

  printf("top of acceptor_optimized, id = %d; len(phase1aPrepare) = %d\n", id, len(phase1aPrepare));
  
  short curRound = -1; // max ballot seen.
  short acceptedNum = -1, acceptedVal = -1;
  short acceptThisVal, rnd;
  do
    :: d_step {
         phase1aPrepare ?? <eval(id), rnd> ->
         printf("acceptor id = %d sees phase1aPrepare len %d: rnd = %d; curRound = %d\n", id, len(phase1aPrepare), rnd, curRound); // len 4, 1, 1. should hold 1,1,2,2
         if
           ::(rnd > curRound) -> curRound = rnd;
              //printf("curRound is now %d\n", curRound);
           :: else
         fi;
         rnd = 0
       }
       // we have to send back on phase1bPromise
       phase1bPromise !! curRound, acceptedNum, acceptedVal;
       //printf("phase1aPrepare ?? was run, and phase1bPromise ! too\n");
       
    :: d_step {
         phase2aAcceptPlease ?? eval(id), rnd, acceptThisVal ->
         if
           ::(rnd >=curRound) -> // ballot in rnd is >= promised, so commit.
             curRound = rnd;
             acceptedNum = rnd;
             acceptedVal = acceptThisVal;
             phase2bLearn !! id, curRound, acceptThisVal;
             printf("acceptor id = %d replied on phase2bLearn\n", id);
           :: else
         fi;
         rnd = 0; acceptThisVal = 0;
       }
       break;
  od
  printf("end of acceptor_optimized id = %d\n", id);
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
      run proposer_optimized(j, j);
    }

    int k = 1;
    for (k : 1 .. ACCEPTORS) {
      run acceptor_optimized(k);
    }

    // if using learn_and_assert_safety, do not also run this:
    //run learner();
  };
}
