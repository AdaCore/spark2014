package P
  with SPARK_Mode => On
is
   -- TU: 1. If the prefix of a record component selection is known statically
   --     to be constrained so that the selected component is not present,
   --     then the component selection (which, in Ada, would raise
   --     Constraint_Error if it were to be evaluated) is illegal.

   type R (D : Boolean) is record
      F1 : Integer;
      case D is
         when False =>
            F2 : Integer;
         when True =>
            F3 : Float;
      end case;
   end record;

   subtype RT is R (True);
   subtype RF is R (False);

   function GRTF2 (X : in RT) return Integer;

   function GRTF3 (X : in RT) return Float;

   function GRFF2 (X : in RF) return Integer;

   function GRFF3 (X : in RF) return Float;

end P;
