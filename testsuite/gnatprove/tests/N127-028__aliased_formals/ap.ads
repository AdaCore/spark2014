package AP
  with SPARK_Mode => On
is

   -- TU: 1. The following reserved words shall not appear in |SPARK| program text
   --     other than in comments:
   --     * **access**, or
   --     * **aliased**.

   procedure Op (A : aliased        Integer; -- error
                 B : aliased in     Integer; -- error
                 C : aliased in out Integer; -- error
                 D : aliased    out Integer; -- error
                 E :         in out Integer) -- OK
   with Depends => (C => (A, B, C),
                    D => (A, B, C),
                    E => (A, B, C, E));
end AP;
