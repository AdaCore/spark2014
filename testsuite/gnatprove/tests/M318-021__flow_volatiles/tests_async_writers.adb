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
   Vol : Integer;  -- TODO: mark as volatile

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

   function Q return Integer
     with Global => (Input => Vol)
   is
   begin
      return Vol;
   end Q;

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
      X := Q;
      Y := Q;
   end Test_02;

   procedure Test_03 (X : out Integer)
     with Global => (Input => Vol)
   is
   begin
      X := 0;
      while X <= 0 loop
         X := Vol;  --  Not stable
      end loop;
   end Test_03;

   procedure Test_04 (X : out Integer)
     with Global => (Input => Vol)
   is
   begin
      X := 0;
      while X <= 0 loop
         X := Q;  --  Not stable
      end loop;
   end Test_04;

end Tests_Async_Writers;
