package UU_Bad
  with SPARK_Mode => On
is
   type R (F : Boolean := True) is record
      case F is
         when False =>
            FI : Integer;
         when True =>
            FF : Float;
      end case;
   end record
     with Unchecked_Union;

   type Root2 is tagged record
      I : Integer;
   end record;

   type Child2 is new Root2 with record
      C : R;
   end record;

end UU_Bad;
