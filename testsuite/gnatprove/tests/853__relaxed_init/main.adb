pragma Warnings(Off, "subprogram * has no effect");

with Ada.Unchecked_Deallocation;

procedure Main with SPARK_Mode is

   type String_Acc is access String;

   procedure Free is new Ada.Unchecked_Deallocation
     (Object => String, Name => String_Acc);

   procedure Foo (S : String) is
      SP : String_Acc (1 .. S'Length) with Relaxed_Initialization;

   begin
      if S'Length = 0 then
         return;
      end if;

      declare
         T : String (1 .. S'Length) := S;
      begin
         SP := new String'(T);
      end;

      pragma Assert (SP.all = S);

      Free (SP);

   end Foo;

   C : constant String (5 .. 9) := "Hello";

begin
   Foo (C);
end Main;
