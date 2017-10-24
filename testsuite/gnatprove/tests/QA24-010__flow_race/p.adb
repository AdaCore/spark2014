package body P with SPARK_Mode, Refined_State => (State => X) is

   X : Boolean := True;

   procedure Flip with SPARK_Mode => Off is
   begin
      X := not X;
   end;

   task body Insider is
   begin
      loop
         Flip;
      end loop;
   end;

end;
