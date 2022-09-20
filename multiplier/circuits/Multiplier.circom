pragma circom 2.0.0;

/*This circuit template checks that c is the multiplication of a and b.*/  

template Multiplier () {  

   // Declaration of signals.  
   signal input a;
   signal input b;
   signal output c;

   var x;

   x = 2222222111232332323;

   log("x hereeee",x);

   // Constraints.
   assert(a>1);

   c <== a * b + x;
   
   c === b * b + x;
}

component main = Multiplier();