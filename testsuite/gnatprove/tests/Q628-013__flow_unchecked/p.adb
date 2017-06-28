with Unchecked_Conversion;

package body P with SPARK_Mode => Off is

   type Foo is new Boolean;

   function "-" is new Unchecked_Conversion (Boolean, Foo);

   procedure Dummy is
      X : Boolean := True;
      Y : Foo     := -X;
   begin
      null;
   end;

end;
