with R; use R;
package body P is

   X : Integer;

   procedure Proc2;
   procedure Proc3;

   procedure Proc with Annotate => (GNATprove, Terminating) is
   begin
      Proc2;
   end Proc;

   procedure Proc2 is
   begin
      Proc3;
   end Proc2;

   procedure Proc3 is
   begin
      while True loop
         null;
      end loop;
   end Proc3;

   procedure Proc4 with Annotate => (GNATprove, Terminating) is
      Result : Boolean;
   begin
      Result := R.Proc3;
   end Proc4;

   procedure Proc5 with Annotate => (GNATprove, Terminating) is
   begin
      if True then
         Proc5;
      end if;
   end Proc5;

   procedure Proc7 with Annotate => (GNATprove, Terminating);

   procedure Proc6 with Annotate => (GNATprove, Terminating) is
   begin
      if True then
         Proc7;
      end if;
   end Proc6;

   procedure Proc7 is
   begin
      if True then
         Proc6;
      end if;
   end Proc7;

   B : Boolean;

begin
   B := False;
   Proc;
   while True loop
      if not B then
         B := True;
         X := 0;
      end if;
   end loop;
end P;
