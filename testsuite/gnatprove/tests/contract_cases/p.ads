package P is  

   Threshold : Integer := 1000;

   procedure Incr_Threshold1 (X : in out Integer) with
     Pre  => X >= 0,
     Post => X = Integer'Min (X'Old + 1, Threshold);

   procedure Incr_Threshold2 (X : in out Integer) with
     Contract_Cases => (X < Threshold  => X = X'Old + 1,
                        X >= Threshold => X = X'Old);

   procedure Incr_Threshold3 (X : in out Integer) with
     Pre  => X >= 0,
     Post => X >= X'Old,
     Contract_Cases => (X < Threshold  => X = X'Old + 1,
                        X >= Threshold => X = X'Old);

   procedure Incr_Threshold4 (X : in out Integer) with
     Pre  => (X < Threshold and not (X >= Threshold))
              or else (not (X < Threshold) and X >= Threshold),
     Post => (if X'Old < Threshold'Old then X = X'Old + 1
              elsif X'Old >= Threshold'Old then X = X'Old);

end P;
