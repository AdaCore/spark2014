package Records_And_Array
  with Abstract_State => (State),
       Initializes    => (X, Z, State)
is

   type RRR is record
      C : Integer := 0;
   end record;

   XXX : RRR;                   -- NOT reported as initialization proved

   X : Integer := 1;            -- reported as initialization proved
   Z : Integer := 3;            -- reported as initialization proved
   Q : Integer := 4;            -- warning: non mentioned in init contract

   task TT1;                    -- NOT reported as initialization proved

   protected Y is
      procedure P;
   private
      B : Boolean := True;
   end Y;                       -- NOT reported as initialization proved

   task type TT2;

   TT2O : TT2;                  -- NOT reported as initialization proved

   type TA is array (Positive range <>) of TT2;

   TAO : TA (1 .. 3);           -- NOT reported as initialization proved

   type TR is record
      T1 : TT2;
   end record;

   TRO : TR;                    -- NOT reported as initialization proved

   type TRA is array (Positive range <>, Positive range <>) of TR;

   TRAO : TRA (1 .. 4, 1 .. 4); -- NOT reported as initialization proved

end Records_And_Array;
