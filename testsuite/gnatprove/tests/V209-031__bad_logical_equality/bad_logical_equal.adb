with Bad_Ext;

procedure Bad_Logical_Equal with SPARK_Mode is
   pragma Annotate (GNATprove, Logical_Equal, "this is not an entity");
   procedure My_Eq_1 with
     Import,
     Annotate => (GNATprove, Logical_Equal);
   function My_Eq_2 (X, Y : Integer) return Boolean is (X = Y) with
     Annotate => (GNATprove, Logical_Equal);
   function My_Eq_3 (X, Y : Integer) return Boolean is (Bad_Ext.My_Eq (X, Y));
   function My_Eq_4 (X : Positive; Y : Integer) return Boolean with
     Import,
     Annotate => (GNATprove, Logical_Equal);
   type My_Bool is new Boolean;
   function My_Eq_5 (X, Y : Integer) return My_Bool with
     Import,
     Annotate => (GNATprove, Logical_Equal);
   function My_Eq_6 (X, Y, Z : Integer) return Boolean with
     Import,
     Annotate => (GNATprove, Logical_Equal);
   function My_Eq_7 return Boolean with
     Import,
     Annotate => (GNATprove, Logical_Equal);
   function My_Eq_8 (X, Y : Integer) return Boolean with
     Import,
     Post => My_Eq_8'Result = (X = Y),
     Annotate => (GNATprove, Logical_Equal);
   pragma Annotate (GNATprove, Inline_For_Proof, My_Eq_8);
   function My_Eq_9 (X, Y : Integer) return Boolean with
     Import,
     Post => My_Eq_9'Result = (X = Y),
     Annotate => (GNATprove, Inline_For_Proof);
   pragma Annotate (GNATprove, Logical_Equal, My_Eq_9);
   G : Boolean;
   function My_Eq_10 (X, Y : Integer) return Boolean with
     Annotate => (GNATprove, Logical_Equal),
     Import,
     Global => G;
begin
   null;
end;
