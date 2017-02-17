package InRange is
   subtype int20 is Integer range 1..20;
   subtype int10 is Integer range 1..10;

   function Add1 (i : int20; j : int10) return Integer
   with Pre => i <= 10,
   Post => Add1'Result <= 20;

   function Add (i : int20; j : int10) return Integer
   with Post => Add'Result <= 40;

   procedure Add_Out (I : in out int20; J : int10)
      with Pre => (I <= 10),
           Post => (I = I'Old + J);

   function Do_It return int10
      with Post => (Do_It'Result <= 10);

end inRange;
