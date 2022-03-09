SetLogFile("cc_X0171star.log");

load "coleman.m";
// SimplifiedModel(X0NQuotient(171,[3^2,19]));
Q := y^2 - (x^8 + 2*x^6 - 8*x^5 + 7*x^4 - 8*x^3 + 10*x^2 - 12*x + 9);
// BadPrimes = 2, 3, 19
p := 5; 
N := 12;
data := coleman_data(Q,p,N);

Qpoints := Q_points(data,1000);

L, v := effective_chabauty(data : Qpoints := Qpoints, e := 40);

printf "L = %o\nQ-points = %o\nv = %o\n", L, Qpoints, v;

if #L eq #Qpoints then
  printf "found all %o Q-points!\n", #Qpoints;
else
  printf "one has to exclude additional %o points\n", #L - #Qpoints;
end if;