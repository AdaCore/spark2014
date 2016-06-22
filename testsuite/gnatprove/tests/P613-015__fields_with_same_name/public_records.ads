with Private_Records; use Private_Records;

package Public_Records with SPARK_Mode is
   type Child is new Root with record
      F : Integer := 1;
   end record;
end Public_Records;
