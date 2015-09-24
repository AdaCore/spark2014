generic
package Gen
  with SPARK_Mode
is
   pragma Annotate (GNATprove, External_Axiomatization);

   Dummy     : aliased Integer := 0;
   Dummy_Ptr : access Integer := Dummy'Access;
private
   pragma SPARK_Mode (On);
end;
