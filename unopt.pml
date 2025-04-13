// Promela model of the basic Paxos algorithm
// (just Synod, single round of agreement on one value).
//
// Extracted from the "Model Checking Paxos in Spin" paper
// by Giorgio Delzanno, Michele Tatarek, and  Riccardo Traverso.
// See https://arxiv.org/pdf/1408.5962

#define ACCEPTORS 3
#define PROPOSERS 3

// Should not be found faulty:
#define MAJORITY (ACCEPTORS / 2 + 1)

// to find a problem when algorithm requirement of quorum not met:
//define MAJORITY 1

#define MAX (ACCEPTORS*PROPOSERS)

typedef mex{
  byte rnd;   // ballot
  short prnd; // previously accepted or commited ballot (highest such number)
  short pval; // previously accepted or commited value
}

chan prepare = [MAX] of {byte, byte};
chan promise = [MAX] of {mex}; 
chan accept = [MAX] of {byte, byte, short};
chan learn = [MAX] of {short, short, short};

inline bprepare(round){
  byte j;
  for (j : 1 .. ACCEPTORS) {
    prepare !!j, round;
  }
}

// broadcast an accept message to acceptors
inline baccept(round, v) {
  byte k;
  for(k : 1 .. ACCEPTORS){
    accept !! k,round,v; 
  }
}

// phase 1: proposer(leader) receives responses to propose from acceptors.
inline recv_proposer(round, count, h, v, hr, hval) {
 d_step {
    promise ?? eval(round), h, v ->   
      if :: count < MAJORITY -> count ++;
       :: else
    fi;
    if :: h > hr -> // taking the highest of the committed values from acceptors.
           hr = h;
           hval = v
       :: else
    fi;
    h = 0; v = 0;
  }
}

// values to acceptors, only once count >= MAJORITY (that is the guard).
inline send_a(round, count, hval, myval, tmp) {
  d_step {
    count >= MAJORITY ->
    if :: hval <0 -> tmp = myval 
       :: else -> tmp = hval
    fi;
  }
  end: baccept(round, tmp);
  break;
}

proctype proposer(int round; short myval) {

  short hr = -1;   // highest commited ballot
  short hval = -1; // highest committed value

  short tmp; // used in send_a
  
  short h; // highest commited ballot temp
  short v; // highest commited value temp
  
  byte count; // proposer's quorum, are we there yet?

  // phase 1: prepare. broadcast ballot to acceptors.
  bprepare(round);
end:  do
       // receive back from acceptors:
    :: recv_proposer(round, count, h, v, hr, hval); 

       // send accept-please-requests, then break and exit
       // to try (unsuccessfully) to prevent bad-end-state errors.
    :: send_a(round, count, hval, myval, tmp) -> break; 
  od
}

inline recv_accept_at_acceptor(i, j, v, rnd, vrnd, vval) {
  atomic {
    accept ?? eval(i), j, v ->
    if ::(j >= rnd) ->
             rnd= j;
             vrnd= j;
             vval =v;
             learn ! i, j, v
       :: else fi;
    j = 0; v = 0 // reset: reduces search state space.
}
}

inline recv_prepare_at_acceptor(i, rnd, prnd, vrnd, vval) {
  atomic {
    prepare ?? eval(i), prnd -> printf("\nREC\n"); // prnd is current ballot.
    if :: (prnd>rnd) -> // jea: shouldn't this be >= ???
          promise ! prnd, vrnd, vval; // a mex{rnd, prnd, pval}
          rnd=prnd;
       :: (prnd <=rnd) -> printf("\nSKIP "); // jea: shouldn't this be < ???
    fi;
    prnd = 0 // reset to reduce state space.
  }
}

proctype acceptor(int i) {

  short rnd = -1;
  short vrnd = -1;
  short vval = -1;
  
  short j;
  short v;
  short prnd;
  
end:  do
    :: recv_accept_at_acceptor(i, j, v, rnd, vrnd, vval);
       if :: vval != -1 -> break;  // exit after accepting a value
          :: else -> skip; // receive again
       fi;
    :: recv_prepare_at_acceptor(i, rnd, prnd, vrnd, vval);
  od
}

init {
  atomic{  
    int j;
    for (j : 1 .. PROPOSERS) {
      run proposer(j, j);
    }

    int i;
    for (i : 1 .. ACCEPTORS) {
      run acceptor(i);
    }
  };
}


inline read_learn_chan_and_assert(id, rnd, lval, lastval, mcount) {
  d_step {
    learn ?? id, rnd, lval ->
    if
      :: mcount [rnd -1] < MAJORITY ->
           mcount [rnd -1]++;
      :: else
    fi;
    if
      :: mcount [rnd -1] >= MAJORITY ->
         if :: (lastval >= 0 && lastval != lval) ->
                 printf("assert error: lastval: %d != lval: %d\n", lastval, lval);
                 assert(false); // equiv to assert(lastval == lval)
            :: (lastval == -1) -> lastval = lval;
            :: else
         fi
         done = true;  // Exit after learning a value
      :: else
    fi;
    id = 0; rnd = 0; lval = 0;
  }
}

// Active learner process that checks for
// consistency (asserts inside read_learn_chan_and_assert).
active proctype learner_assert_consistency() {
  short lastval = -1, id, rnd, lval;
  byte mcount[PROPOSERS];
  bool done = false;
end:  do
    :: read_learn_chan_and_assert(id, rnd, lval, lastval, mcount);
    :: done -> break;
  od
}
