--  =================
--  = Async_Writers =
--  =================
--
--  * Something might, at any time, update the value in this
--    volatile. Writing to it is completely pointless, it is
--    effectively a black hole. (Only with async_readers will
--    it be meaningful to write to such an object.) In a way
--    this means this is an input_only volatile.
--
--  * Having this volatile appear as an output makes no sense,
--    so we only need to consider the case where it is a global
--    input.

package body Tests_Async_Writers
  with Refined_State => (State_With_Async_Writers => Vol)
is
   Vol : Integer
    with Volatile, Async_Writers, Effective_Reads;

   ----------------------------------------------------------------------
   --  The following are "correct" contracts and should not raise any
   --  errors.
   ----------------------------------------------------------------------

   procedure P (X, Y : out Integer)
     with Global  => (Input => Vol),
          Depends => (X => Vol,
                      Y => Vol)
   is
   begin
      X := Vol;
      Y := Vol;
   end P;

   -- This is illegal.  A Volatile object with Async_Writers true cannot appear
   -- in an expression and therefore cannot be the return expression of the
   -- function.  If it was allowed the function would have a side-effect.
   -- This is different to SPARK 2005.
   function Q return Integer
     with Global => (Input => Vol)
   is
   begin
      return Vol;
   end Q;

   -- Rewrite Q as a procedure
   procedure Proc_Q (V_Out : out Integer)
      with Global  => (Input => Vol),
           Depends => (V_Out => Vol)
   is
   begin
      V_Out := Vol;
   end Proc_Q;

   procedure Test_01 (X, Y : out Integer)
     with Global  => (Input => Vol),
          Depends => (X => Vol,
                      Y => Vol)
   is
   begin
      P (X, Y);
   end Test_01;

   procedure Test_02 (X, Y : out Integer)
     with Global  => (Input => Vol),
          Depends => (X => Vol,
                      Y => Vol)
   is
   begin
      Proc_Q (X);
      Proc_Q (Y);
   end Test_02;

   procedure Test_03 (X : out Integer)
      with Global  => (Input => Vol),
           Depends => (X => Vol)
   is
   begin
      X := 0;
      while X <= 0 loop
         X := Vol;  --  Not stable
      end loop;
   end Test_03;

   procedure Test_04 (X : out Integer)
      with Global  => (Input => Vol),
           Depends => (X => Vol)
   is
   begin
      X := 0;
      while X <= 0 loop
         Proc_Q (X);  --  Not stable
      end loop;
   end Test_04;

begin
   Vol := 0;
end Tests_Async_Writers;
