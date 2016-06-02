package InRange is
   subtype int20 is Integer range 1..20;
   subtype int10 is Integer range 1..10;

   protected type PT is
      entry Add_Out (I : in out int20; J : int10)
         with Pre => (I <= 10),
              Post => (I = I'Old + J);
   end PT;

   PO : PT;

   procedure Do_It;

end inRange;
