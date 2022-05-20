package body Infinite_Sequences with SPARK_Mode is
   use Maps;

   function First (S : Sequence) return Big_Positive is (S.First);

   function Last (S : Sequence) return Big_Natural is (S.Last);

   function Is_Valid
     (Fst : Big_Positive;
      Lst : Big_Natural;
      M   : Maps.Map) return Boolean
   is
     (Lst >= Fst - 1
      and then (for all I in Interval'(Fst, Lst) => Has_Key (M, I))
      and then (for all I of M => In_Range (I, Fst, Lst)));
   --  A sequence from F to L is a map with the integers between F and L as keys

   function Get (S : Sequence; I : Big_Positive) return Integer is
     (Get (S.Content, I));

   function Empty (Fst : Big_Positive) return Sequence is
     (First   => Fst,
      Last    => Fst - 1,
      Content => Empty_Map);

   function "=" (X, Y : Sequence) return Boolean is
     (X.First = Y.First and then X.Last = Y.Last
      and then X.Content = Y.Content);

   function "<=" (X, Y : Sequence) return Boolean is
     (Y.First <= X.First and then X.Last <= Y.Last
      and then X.Content <= Y.Content);

   function Concat (S1 : Sequence; I2 : Integer; S3 : Sequence) return Sequence is
      Content : Map := S1.Content;
   begin
      if S1.Last < S1.First then
         Content := S3.Content;
         Content := Add (Content, S1.First, I2);
      else
         Content := Add (Content, S1.Last + 1, I2);
         declare
            I : Big_Positive := S3.First;
         begin
            while I <= S3.Last loop
               Content := Add (Content, I, Get (S3.Content, I));
               pragma Loop_Variant (Decreases => S3.Last - I);
               pragma Loop_Invariant (I <= S3.Last);
               pragma Loop_Invariant (S1.Content <= Content);
               pragma Loop_Invariant (Has_Key (Content, S1.Last + 1));
               pragma Loop_Invariant (Get (Content, S1.Last + 1) = I2);
               pragma Loop_Invariant
                 (for all K in Interval'(S3.First, I) =>
                      Has_Key (Content, K)
                  and then Get (Content, K) = Get (S3, K));
               pragma Loop_Invariant
                 (for all K of Content => In_Range (K, S1.First, I));
               I := I + 1;
            end loop;
         end;
      end if;
      return (First => S1.First, Last => S3.Last, Content => Content);
   end Concat;
end Infinite_Sequences;
