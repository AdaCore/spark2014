pragma SPARK_Mode;

package T1Q3C
is

  type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

  procedure NextDay_A(Today: in Day; Tomorrow: out Day)
    with Post => (Today=Mon and Tomorrow=Tue) or else
                 (Today=Tue and Tomorrow=Wed) or else
                 (Today=Wed and Tomorrow=Thu) or else
                 (Today=Thu and Tomorrow=Fri) or else
                 (Today=Fri and Tomorrow=Sat) or else
                 (Today=Sat and Tomorrow=Sun) or else
                 (Today=Sun and Tomorrow=Mon);

  procedure NextDay_B(Today: in Day; Tomorrow: out Day)
    with Post => (Today=Mon and Tomorrow=Tue) or else
                 (Today=Tue and Tomorrow=Wed) or else
                 (Today=Wed and Tomorrow=Thu) or else
                 (Today=Thu and Tomorrow=Fri) or else
                 (Today=Fri and Tomorrow=Sat) or else
                 (Today=Sat and Tomorrow=Sun) or else
                 (Today=Sun and Tomorrow=Mon);

end T1Q3C;
