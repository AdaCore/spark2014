with Ada.Text_IO;

package body P is

   protected body PO is
      entry My_Text_Entry when True is
         subtype My_Float is Float range 0.0 .. 1.0;

         package My_Float_Text_IO is new Ada.Text_IO.Float_IO (My_Float);
      begin
         My_Float_Text_IO.Put (My_Float'First);
      end;

   end;

end P;
