pragma SPARK_Mode(On);
package Messages_Wrapper is
   type Checksum_Type is mod 2**16;

   function Compute_Checksum (Data : in String) return Checksum_Type;
end Messages_Wrapper;
