package TP is
   task Singl_Task;

   B4 : Integer := 0
     with Part_Of => Singl_Task;

   protected Singl_Prot is
      function Get_Content return Integer;
   private
      Content : Integer := 0;
   end Singl_Prot;

   Give_Zero : Boolean := True
     with Part_Of => Singl_Prot;

   Give_One : Boolean := True
     with Part_Of => Singl_Prot;
end TP;
