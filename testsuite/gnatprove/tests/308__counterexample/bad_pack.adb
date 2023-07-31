pragma Ada_2012;
package body Bad_Pack with
   SPARK_Mode => On
is
   procedure Foo (X : in out Boolean; Y : in Boolean) is
   begin
      if Y then
         X := not X;
      end if;
   end Foo;
end Bad_Pack;
