--  =================
--  = Async_Readers =
--  =================
--
--  * Something is consuming data that is being written, either step
--    by step or constantly
--
--  * This something may be a stream, so writing the same thing twice is
--    ok (i.e. writes are effective)
--
--  * This something may have state, so the behaviour of the system may
--    change with every value we feed in
--
--  * You might want to read back the value you just wrote in - this
--    read only depends on what you wrote last.

package body Tests_Async_Readers
  with Refined_State => (State_With_Async_Readers => Vol)
is
   Vol : Integer
    with Volatile, Async_Readers;

   ----------------------------------------------------------------------
   --  The following are "correct" contracts and should not raise any
   --  errors.
   ----------------------------------------------------------------------

   procedure P (X, Y : in     Integer;
                Z    :    out Integer)
     with Global  => (Output => Vol),
          Depends => (Vol => (X, Y),
                      Z   => Y)
   is
   begin
      Vol := X;
      Vol := Y;
      Z   := Vol;
   end P;

   procedure Calling_P (X, Y : in     Integer;
                        Z, W :    out Integer)
     with Global => (Output => Vol),
                     Depends => (Vol => (X, Y),
                                 Z   => Y,
                                 W   => (X, Y))  -- hmmm, interesting
                                                 -- Yes but conservative
   is
   begin
      P (X, Y, Z);
      W := Vol;
   end Calling_P;

   procedure Q (X, Y : in     Integer;
                Z, W :    out Integer)
     with Global  => (In_Out => Vol),
          Depends => (Vol => (X, Y),  --  Vol is not an input here
                                      -- it has no asyncronous writers.
                                      -- Previous values have been consumed
                                      -- by asynchronous readers
                                      -- It would be the same in S2005
                                      -- mode in own variable

                      Z   => Vol,
                      W   => Y)       --  and not Vol because Vol has
                                      -- no asynchronous writers
   is
   begin
      Z   := Vol;
      Vol := X;
      Vol := Y;
      W   := Vol;
   end Q;

   procedure Calling_Q (X, Y, N : in     Integer;
                        Z, W, V :    out Integer)
     with Global  => (Output => Vol),
          Depends => (Vol => (X, Y, N),  -- Vol is not an input here
                      Z   => N,          -- It has no asynchronous writers
                      W   => Y,
                      V   => (X, Y, N))  -- Conservative again
   is
   begin
      Vol := N;
      Q (X, Y, Z, W);
      V := Vol;
   end Calling_Q;

   procedure Calling_P_Again (X, Y, N : in     Integer;
                              Z, W, V :    out Integer)
     with Global  => (Output  => Vol),
          Depends => (Vol => (X, Y), -- Vol is not an input here
                      Z   => Y,      -- It has no asynchronous writers
                      W   => N,
                      V   => (X, Y)) -- Conservative
   is
   begin
      Vol := N;   --  No flow error here because Vol is not an input
                  -- and N is used in determing the value of W
      W := Vol;
      P (X, Y, Z);
      V := Vol;
   end Calling_P_Again;

   --  The function and procedure here should behave the same.

   procedure R_Proc (Z : out Integer)
     with Global  => (Input => Vol),
          Depends => (Z => Vol)
   is
   begin
      Z := Vol;
   end R_Proc;

   function R_Func return Integer
     with Global => (Input => Vol)
   is
   begin
      return Vol;
   end R_Func;

   procedure Calling_R (A, B    : in     Integer;
                        X, Y, Z :    out Integer)
     with Global  => (In_Out => Vol),
          Depends => (Vol => (A, B), -- Vol does not depend on itself
                      X   => Vol,
                      Y   => A,     --  This is quite different than before
                                    -- Not because of the differnce between
                                    -- a procedure and a function but because
                                    -- of the surrounding statements.
                                    -- See example below
                      Z   => B)
   is
   begin
      X   := R_Func;
      Vol := A;
      R_Proc (Y);
      Vol := B;
      Z   := Vol;
   end Calling_R;

   procedure Calling_R_Again (A, B    : in     Integer;
                              X, Y, Z :    out Integer)
     with Global  => (In_Out => Vol),
          Depends => (Vol => (A, B), -- Vol does not depend on itself
                      X   => Vol,    -- We have the same dependencies as
                      Y   => A,      -- in the previous example.
                      Z   => B)
   is
   begin
      R_Proc (X);
      Vol := A;
      Y := R_Func;
      Vol := B;
      Z   := Vol;
   end Calling_R_Again;

end Tests_Async_Readers;
