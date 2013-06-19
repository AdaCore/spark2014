package body Admin
is
   type PrivilegeT is (UserOnly,
                       Guard,
                       AuditManager,
                       SecurityOfficer);

   subtype AdminPrivilegeT is PrivilegeT range Guard .. SecurityOfficer;

   type OpAndNullT is (NullOp,
                       ArchiveLog,
                       UpdateConfigData,
                       OverrideLock,
                       ShutdownOp);

   subtype OpT is OpAndNullT range ArchiveLog .. ShutdownOp;

   type T is
      record
         RolePresent : PrivilegeT;
         CurrentOp   : OpAndNullT;
      end record;

   type AvailOpsT is array (OpT) of Boolean;
   type PrivToAvailOpsT is array (AdminPrivilegeT) of AvailOpsT;

   IsAvailable : constant PrivToAvailOpsT :=
     PrivToAvailOpsT'(Guard           => AvailOpsT'(
                                                    OverrideLock => True,
                                                    others       => False
                                                   ),
                      AuditManager    => AvailOpsT'(
                                                    ArchiveLog => True,
                                                    others     => False
                                                   ),
                      SecurityOfficer => AvailOpsT'(
                                                    UpdateConfigData => True,
                                                    ShutdownOp       => True,
                                                    others           => False
                                                   ));


   function AllowedOp (TheAdmin : T;
                       Op       : OpT) return Boolean
   is
      (IsAvailable(TheAdmin.RolePresent)(Op));
end Admin;
