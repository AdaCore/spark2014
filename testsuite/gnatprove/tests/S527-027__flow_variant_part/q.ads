package Q is
   X : Positive;  --  variable

   type T1 is record
      C : String (1 .. X);       --  variable input in constraint
   end record;

   type T2 (D : Boolean) is record
      case D is
         when True =>
            C : String (1 .. X); --  variable input in constraint
         when False =>
            null;
      end case;
   end record;
end;
