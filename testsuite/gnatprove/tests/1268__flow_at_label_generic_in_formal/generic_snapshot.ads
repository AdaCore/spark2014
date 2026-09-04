generic
   Initial : in Integer;
package Generic_Snapshot with SPARK_Mode is
   procedure Read_Captured (Later : Integer; Output : out Integer)
   with Depends => (Output => Initial, null => Later);
end Generic_Snapshot;
