with Stack;    use type Stack.T;

package Records_ProofFuncs
is
   type Unsigned_Byte is range 0 .. 255;

   type Command_T is (Increment_A,
                      Assign_A,
                      Swap);

   type Pair is record
      A : Unsigned_Byte;
      B : Unsigned_Byte;
   end record;

   Null_Pair : constant Pair := Pair'(A => 0,
                                      B => 0);

   type Optional_Pair is record
      Exists   : Boolean;
      The_Pair : Pair;
   end record;

   Null_Optional_Pair : constant Optional_Pair :=
     Optional_Pair'(Exists   => False,
                    The_Pair => Null_Pair);
   --  No rule declared on purpose, we will do this on an as-needed
   --  bases.

   type Packet is record
      Data    : Pair;
      Command : Command_T;
   end record;

   type Part_Private is record
      Unrelated : Boolean;
      Hidden    : Stack.T;
   end record;

   subtype Record_Subtype is Packet;

   function F_Of_Pair (P : in Pair) return Boolean with Annotate => (GNATprove, Always_Return);
end Records_ProofFuncs;
