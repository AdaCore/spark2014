package Ext is
   function My_Eq (X, Y : Integer) return Boolean with
     Annotate => (GNATprove, Logical_Equal);
end Ext;
