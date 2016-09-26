with GNAT.OS_Lib;            use GNAT.OS_Lib;
package body R is
   Y : Integer;
   B : Boolean;

   protected type PT is
      entry E;
      procedure P;
   private
      Flag : Boolean := True;
      X    : My_Integer := 1;
   end;

   protected body PT is
      entry E when Flag is
      begin
         for I in My_Integer'Range loop
            E;
            Flag := False;
         end loop;
      end E;

      procedure P is
      begin
         while True loop
            null;
         end loop;
      end P;
   end PT;

   procedure Proc1 is
   begin
      if True then
         Proc1;
      end if;
   end Proc1;

   procedure Proc2 is
   begin
      OS_Exit (0);
   end Proc2;

   function Proc3 return Boolean is
   begin
      while True loop
         return True;
      end loop;
      return False;
   end Proc3;

   procedure Proc4 is
   begin
      OS_Exit (1);
   end Proc4;

begin
   Proc1;
   OS_Exit (0);
   Proc2;
end R;
