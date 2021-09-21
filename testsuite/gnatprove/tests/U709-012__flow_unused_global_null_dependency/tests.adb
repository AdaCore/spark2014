with Gen; with Gen_State;

package body Tests with SPARK_Mode is

   Bool : Boolean; -- subprograms need to have an effect to trigger the messages

   procedure Gen_Wo_Depends is
      package Inst is new Gen;
   begin
      Bool := True;
      Inst.Run;
   end Gen_Wo_Depends;

   procedure Gen_With_Depends is
      package Inst is new Gen_State;
   begin
      Bool := True;
      Inst.Run;
   end Gen_With_Depends;

   procedure Local_Wo_Depends is
      A : Boolean;

      procedure Run with Pre => True is
      begin
         A := True;
      end Run;

   begin
      Bool := True;
      Run;
   end Local_Wo_Depends;

   procedure Local_With_Depends is
      A : Boolean;

      procedure Run with
        Global  => (Output => A),
        Depends => (A => null)
      is
      begin
         A := True;
      end Run;

   begin
      Bool := True;
      Run;
   end Local_With_Depends;
end Tests;
