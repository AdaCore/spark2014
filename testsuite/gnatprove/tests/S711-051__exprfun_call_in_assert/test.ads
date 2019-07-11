package Test with
   SPARK_Mode
is

   type Field_Type is (Initial, Destination, Source, Final);
   type Element_Type is private;
   type Array_Type is array (Field_Type) of Element_Type;
   type Context_Type is private;

   function Context_Field (Context : Context_Type) return Field_Type;

   procedure Verify_Destination (Context : in out Context_Type) with
     Pre => Context_Field (Context) = Initial,
     Post => Context_Field (Context) = Destination;

private

   type State_Type is (Valid, Invalid);
   type Element_Type (State : State_Type := Invalid) is
      record
         case State is
            when Valid | Invalid =>
               null;
         end case;
      end record;

   type Context_Type is
      record
         Field  : Field_Type;
         Elements : Array_Type;
      end record;

end Test;
