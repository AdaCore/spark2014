pragma Extensions_Allowed (All_Extensions);

package body Generic_Snapshot is
   procedure Read_Captured (Later : Integer; Output : out Integer) is
      Value : Integer := Initial;
   begin
      <<Capture>>
      Value := Later;

      --  The snapshot use passes through generic-formal mapping again and
      --  must retain its internal identity rather than revisit Value.

      Output := Value'At (Capture);
   end Read_Captured;
end Generic_Snapshot;
