with Ada.Real_Time;

package body Nested_PB_Call is

   protected PO is
      entry Dummy with
         Global => Ada.Real_Time.Clock_Time;
   end;

   protected body PO is
      entry Dummy when True is
         package P is
            X : Integer;
         end;

         package body P is
         begin
            X := 0;
            delay until Ada.Real_Time.Clock;
         end;
      begin
         null;
      end;
   end;

end;
