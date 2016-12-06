package Terminating_Annotations with SPARK_Mode is
    function F_Not_SPARK (X : Natural) return Natural;
    pragma Annotate (GNATprove, Terminating, F_Not_SPARK);

    procedure Not_SPARK;
    function F_Call (X : Natural) return Natural;
    pragma Annotate (GNATprove, Terminating, F_Call);
end Terminating_Annotations;
