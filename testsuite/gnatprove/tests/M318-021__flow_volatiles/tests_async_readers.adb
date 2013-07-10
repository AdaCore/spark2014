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
   Vol : Integer;  -- TODO: mark as volatile

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
   is
   begin
      P (X, Y, Z);
      W := Vol;
   end Calling_P;

   procedure Q (X, Y : in     Integer;
                Z, W :    out Integer)
     with Global  => (In_Out => Vol),
                      Depends => (Vol => (Vol, X, Y),    --  should this be implicit?
                                  Z   => Vol,
                                  W   => Y)              --  and not vol?
   is
   begin
      Z   := Vol;
      Vol := X;
      Vol := Y;
      W   := Vol;
   end Q;

   procedure Calling_Q (X, Y, N : in     Integer;
                        Z, W, V :    out Integer)
     with Global  => (In_Out => Vol),
          Depends => (Vol => (Vol, X, Y, N),
                      Z   => (Vol, N),
                      W   => Y,
                      V   => (Vol, X, Y, N))
   is
   begin
      Vol := N;
      Q (X, Y, Z, W);
      V := Vol;
   end Calling_Q;

   procedure Calling_P_Again (X, Y    : in     Integer;
                              Z, W, V :    out Integer)
     with Global => (In_Out => Vol),
                     Depends => (Vol => (Vol, X, Y),
                                 Z   => Y,
                                 W   => Vol,
                                 V   => (Vol, X, Y))
   is
   begin
      --  Vol := N;   --  would this raise an "import not used" flow error?
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
          Depends => (Vol => (Vol, A, B),
                      X   => Vol,
                      Y   => A,     --  This is quite different than before
                      Z   => B)
   is
   begin
      X   := R_Func;
      Vol := A;
      R_Proc (Y);
      Vol := B;
      Z   := Vol;
   end Calling_R;

end Tests_Async_Readers;
