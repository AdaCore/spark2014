package body P is

  subtype T is Integer range 1 .. 10;

   procedure Proc is
     X : T := 9;
   begin
      null;
   end Proc;
end P;
