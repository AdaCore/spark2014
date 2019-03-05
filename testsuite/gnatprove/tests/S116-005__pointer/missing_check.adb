procedure Missing_Check with SPARK_Mode is
    type Ptr is access Integer;
    type Ptr_Ptr is access Ptr;

    procedure Bad (X : Ptr; Y : out Ptr_Ptr) with
      Pre => True
    is
    begin
       Y := new Ptr'(X); -- X is of mode in, it cannot be moved
    end bad;
begin
    null;
end Missing_Check;
