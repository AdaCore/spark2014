with Ada.Real_Time;

package External_Model with SPARK_Mode is
   function Random_Wait return Ada.Real_Time.Time with
     Annotate => (GNATprove, Always_Return);
end External_Model;
