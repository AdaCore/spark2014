with Private_Tagged; use Private_Tagged;
package Private_Tagged_Ext with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is
   type V is new Pool_Specific_Access with record
      F : Integer;
   end record;
   function Allocate (X : Integer) return V with
     Global => null,
     Import;
end Private_Tagged_Ext;
