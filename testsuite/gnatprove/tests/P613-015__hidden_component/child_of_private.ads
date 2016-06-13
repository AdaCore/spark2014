with Private_Root; use Private_Root;
package Child_Of_Private with SPARK_Mode is
   type Child is new Root with private;

   procedure P;
private
   type Child is new Root with record
      Hidden_G : Integer;
   end record;
end Child_Of_Private;
