pragma SPARK_Mode;
function IndexBis (C : String; S : String) return Natural is
begin
   if S'Length = 0 or else C'Length = 0 then
      return 0;
   else
      declare
         Courant : Positive := S'First;
      begin
         loop
            pragma Loop_Invariant
              (Courant in S'Range
               and then not (for some I in S'First .. Courant - 1 => (for some J in C'Range => S (I) = C (J))));
            declare
               Possible : Positive := C'First;
            begin
               loop
                  pragma Loop_Invariant
                    (Courant in S'Range
                     and then not (for some I in S'First .. Courant - 1 => (for some J in C'Range => S (I) = C (J)))
                     and then Possible in C'Range
                     and then not (for some J in C'First .. Possible - 1 => S (Courant) = C (J)));
                  if S (Courant) = C (Possible) then
                     return Courant;
                  elsif Possible < C'Last then
                     Possible := Positive'Succ (Possible);
                  else
                     exit;
                  end if;
               end loop;
            end;
            if Courant < S'Last then
               Courant := Positive'Succ (Courant);
            else
               return 0;
            end if;
         end loop;
      end;
   end if;
end IndexBis;
