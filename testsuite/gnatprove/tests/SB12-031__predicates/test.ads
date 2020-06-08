package Test with
  SPARK_Mode
is

   type Int is range 0 .. 2**8;

   function Valid_Context (Value : Int) return Boolean is
     (Value /= 255);

   type Context is
      record
         Value : Int;
      end record with
     Predicate => Valid_Context (Value);
--       Predicate => Value /= 255;  --  predicate can be proved if expression is used directly

   procedure Set_Value (Ctx : in out Context);

end Test;
