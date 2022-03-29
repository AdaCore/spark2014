package Bad_Ext is
   function My_Eq (X, Y : Integer) return Boolean is (X = Y) with
     Annotate => (GNATprove, Logical_Equal);
end Bad_Ext;
