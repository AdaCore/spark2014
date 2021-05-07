package UU_mem
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

   type Holder is record
      C : R;
   end record;

   subtype FR is R (True);

   function C (Left, Right : in R) return Boolean;

   function C2 (Left, Right : in FR) return Boolean;

   function C3 (Left : in FR;
                Right : in R) return Boolean;

   function C4 (Left, Right : in Holder) return Boolean;

   type Root1 is tagged record
      C : R;
   end record;

   function C5 (Left, Right : in Root1'Class) return Boolean;

   type Root2 is tagged record
      I : Integer;
   end record;

   type Child2 is new Root2 with record
      C : FR;
   end record;

   function C6 (Left, Right : in Root2'Class) return Boolean;

   function C7 (Left : in FR;
                Right : in R) return Boolean;

   function C8 (Left : in FR;
                Right : in R) return Boolean;

end UU_mem;
