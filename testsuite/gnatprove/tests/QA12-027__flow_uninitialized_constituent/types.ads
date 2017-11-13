with Remote;
with Remote_SPARK;
package Types
is
   type T is private;
   type TT is private;
   type TTT is private;

private
   pragma SPARK_Mode (Off);
   type Null_Tagged_Record is tagged record
      null;
   end record;

   type T is access Null_Tagged_Record;
   type TT is new Remote.B;
   type TTT is new Remote_SPARK.B;
end;
