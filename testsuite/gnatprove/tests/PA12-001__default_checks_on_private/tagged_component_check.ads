package Tagged_Component_Check with SPARK_Mode is
   package P is
      function Hide (X : Integer) return Integer;
      pragma Annotate (GNATprove, Terminating, Hide);
   private
      pragma SPARK_Mode (Off);
      function Hide (X : Integer) return Integer is (X);
   end P;
   use P;

   package Q is
      package P1 is
         type Root is tagged record
            F : Natural := Hide (0); --@RANGE_CHECK:NONE
         end record;
         type C is new Root with record
            G : Natural := Hide (1); --@RANGE_CHECK:NONE
         end record;
      end P1;

      package P2 is
         type Root is tagged record
            F : Natural := Hide (2); --@RANGE_CHECK:NONE
         end record;
         type C is new Root with private;
      private
         type C is new Root with record
            G : Natural := Hide (3); --@RANGE_CHECK:FAIL
         end record;
      end P2;

      package P3 is
         type Root is tagged record
            F : Natural := Hide (4); --@RANGE_CHECK:FAIL
         end record;
         type C is tagged private;
      private
         type C is new Root with record
            G : Natural := Hide (5); --@RANGE_CHECK:FAIL
         end record;
      end P3;

      package P4 is
         type Root is tagged record
            F : Natural := Hide (6); --@RANGE_CHECK:NONE
         end record;
         type C is new Root with private;
      private
         pragma SPARK_Mode (Off);
         type C is new Root with record
            G : Natural := Hide (7); --@RANGE_CHECK:NONE
         end record;
      end P4;

      package P5 is
         type Root is tagged record
            F : Natural := Hide (8); --@RANGE_CHECK:NONE
         end record;
         type C is tagged private;
      private
         pragma SPARK_Mode (Off);
         type C is new Root with record
            G : Natural := Hide (9); --@RANGE_CHECK:NONE
         end record;
      end P5;

      type D1 is new P1.C with record
         H : Natural := Hide (10); --@RANGE_CHECK:NONE
      end record;

      type D2 is new P2.C with record
         H : Natural := Hide (11); --@RANGE_CHECK:NONE
      end record;

      type D3 is new P3.C with record
         H : Natural := Hide (12); --@RANGE_CHECK:NONE
      end record;

      type D4 is new P4.C with record
         H : Natural := Hide (13); --@RANGE_CHECK:NONE
      end record;

      type D5 is new P5.C with record
         H : Natural := Hide (14); --@RANGE_CHECK:NONE
      end record;
   end Q;

   package R is
      package P1 is
         type Root is tagged record
            F : Natural := Hide (15); --@RANGE_CHECK:NONE
         end record;
         type C is new Root with record
            G : Natural := Hide (16); --@RANGE_CHECK:NONE
         end record;
      end P1;

      package P2 is
         type Root is tagged record
            F : Natural := Hide (17); --@RANGE_CHECK:NONE
         end record;
         type C is new Root with private;
      private
         type C is new Root with record
            G : Natural := Hide (18); --@RANGE_CHECK:FAIL
         end record;
      end P2;

      package P3 is
         type Root is tagged record
            F : Natural := Hide (19); --@RANGE_CHECK:FAIL
         end record;
         type C is tagged private;
      private
         type C is new Root with record
            G : Natural := Hide (20); --@RANGE_CHECK:FAIL
         end record;
      end P3;

      package P4 is
         type Root is tagged record
            F : Natural := Hide (21); --@RANGE_CHECK:NONE
         end record;
         type C is new Root with private;
      private
         pragma SPARK_Mode (Off);
         type C is new Root with record
            G : Natural := Hide (22); --@RANGE_CHECK:NONE
         end record;
      end P4;

      package P5 is
         type Root is tagged record
            F : Natural := Hide (23); --@RANGE_CHECK:NONE
         end record;
         type C is tagged private;
      private
         pragma SPARK_Mode (Off);
         type C is new Root with record
            G : Natural := Hide (24); --@RANGE_CHECK:NONE
         end record;
      end P5;

      type D1 is new P1.C with private;

      type D2 is new P2.C with private;

      type D3 is new P3.C with private;

      type D4 is new P4.C with private;

      type D5 is new P5.C with private;

   private

      type D1 is new P1.C with record
         H : Natural := Hide (25); --@RANGE_CHECK:FAIL
      end record;

      type D2 is new P2.C with record
         H : Natural := Hide (26); --@RANGE_CHECK:FAIL
      end record;

      type D3 is new P3.C with record
         H : Natural := Hide (27); --@RANGE_CHECK:FAIL
      end record;

      type D4 is new P4.C with record
         H : Natural := Hide (28); --@RANGE_CHECK:FAIL
      end record;

      type D5 is new P5.C with record
         H : Natural := Hide (29); --@RANGE_CHECK:FAIL
      end record;
   end R;

   package S is
      package P1 is
         type Root is tagged record
            F : Natural := Hide (30); --@RANGE_CHECK:FAIL
         end record;
         type C is new Root with record
            G : Natural := Hide (31); --@RANGE_CHECK:FAIL
         end record;
      end P1;

      package P2 is
         type Root is tagged record
            F : Natural := Hide (32); --@RANGE_CHECK:FAIL
         end record;
         type C is new Root with private;
      private
         type C is new Root with record
            G : Natural := Hide (33); --@RANGE_CHECK:FAIL
         end record;
      end P2;

      package P3 is
         type Root is tagged record
            F : Natural := Hide (34); --@RANGE_CHECK:FAIL
         end record;
         type C is tagged private;
      private
         type C is new Root with record
            G : Natural := Hide (35); --@RANGE_CHECK:FAIL
         end record;
      end P3;

      package P4 is
         type Root is tagged record
            F : Natural := Hide (36); --@RANGE_CHECK:FAIL
         end record;
         type C is new Root with private;
      private
         pragma SPARK_Mode (Off);
         type C is new Root with record
            G : Natural := Hide (37); --@RANGE_CHECK:NONE
         end record;
      end P4;

      package P5 is
         type Root is tagged record
            F : Natural := Hide (38); --@RANGE_CHECK:NONE
         end record;
         type C is tagged private;
      private
         pragma SPARK_Mode (Off);
         type C is new Root with record
            G : Natural := Hide (39); --@RANGE_CHECK:NONE
         end record;
      end P5;

      type D1 is tagged private;

      type D2 is tagged private;

      type D3 is tagged private;

      type D4 is tagged private;

      type D5 is tagged private;

   private

      type D1 is new P1.C with record
         H : Natural := Hide (40); --@RANGE_CHECK:FAIL
      end record;

      type D2 is new P2.C with record
         H : Natural := Hide (41); --@RANGE_CHECK:FAIL
      end record;

      type D3 is new P3.C with record
         H : Natural := Hide (42); --@RANGE_CHECK:FAIL
      end record;

      type D4 is new P4.C with record
         H : Natural := Hide (43); --@RANGE_CHECK:FAIL
      end record;

      type D5 is new P5.C with record
         H : Natural := Hide (44); --@RANGE_CHECK:FAIL
      end record;
   end S;
end Tagged_Component_Check;
