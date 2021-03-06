puts "1..11"
h = {'a' =>10,'b' => 18+2 , 'c' => 30}
h{'d'} = 100
puts "#{h{'a'} == 10 ? 'ok' : 'nok'} 1 - h{'a'}"
puts "#{h<b> == 20 ? 'ok' : 'nok'} 2 - h<b>"
h_idx = 'c'
puts "#{h{h_idx} == 30 ? 'ok' : 'nok'} 3 - h{c_idx}"
puts "#{h{'d'} == 100 ? 'ok' : 'nok'} 4 - h{'d'}"

delete(h, 'd')
t = 4

for kv in h do
    puts "ok #{t += 1} - hash key iteration"
end

h<d> = ['nok','ok']
puts "#{ h<d>[1] } 8 - HoA"

def test_hash_args(x, h_args)
    puts "ok #{ x } - fixed arg"
    for kv in h_args do
       k = key kv
       v = value kv
       puts "#{ ((k~k) eq v) ? 'ok' : 'nok'} - hash slurpy arg (#{k})"
    end
end
test_hash_args 9, 'z' => 'zz', 'y' => 'yy'

