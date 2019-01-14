with Info;

package Test with SPARK_Mode
is
   procedure Get (N : out Integer)
   with
     Global  =>
       (Proof_In => Info.Valid,
        Input    => Info.State),
     Pre => Info.Is_Valid;

end Test;
