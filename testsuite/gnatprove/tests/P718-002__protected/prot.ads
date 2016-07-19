package Prot is

   protected type Obj is
      function F return Integer;
   end Obj;


   P : Prot.Obj;
end Prot;
