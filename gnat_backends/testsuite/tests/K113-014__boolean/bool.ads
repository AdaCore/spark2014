package Bool is
   type OpAndNullT is (
                       NullOp,
                       ArchiveLog,
                       UpdateConfigData,
                       OverrideLock,
                       ShutdownOp
                      );

   subtype OpT is OpAndNullT range ArchiveLog..ShutdownOp;

   type AvailOpsT is array (OpT) of Boolean;
end Bool;
