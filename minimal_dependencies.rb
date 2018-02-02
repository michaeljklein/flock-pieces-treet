#!/usr/bin/env ruby


cabal_file = Dir['*.cabal'].first
puts "found cabal file:", cabal_file

whole_file       = File.read(cabal_file)
whole_file_lines = File.read(cabal_file).lines

before_depends = whole_file_lines.take_while{|x|!x.match(/build-depends/)}
build_depends  = [whole_file_lines.drop_while{|x|!x.match(/build-depends/)}.first]
depends        = whole_file_lines.drop_while{|x|!x.match(/build-depends/)}.drop(1).take_while{|x|x.match(/^\s+,/)}
after_depends  = whole_file_lines.drop_while{|x|!x.match(/build-depends/)}.drop(1).drop_while{|x|x.match(/^\s+,/)}

# puts 'before_depends', before_depends
# puts 'build_depends ', build_depends 
# puts 'depends       ', depends       
# puts 'after_depends ', after_depends 


def skips(x)
  (0..x.length-1).map do |i|
    (y = x.dup).delete_at(i);y
  end
end


unused_indices = []

skips(depends).each_with_index do |depends_skip, i|
  puts "skipping:", depends[i]
  File.open cabal_file, 'w' do |f|
    f.write (before_depends + build_depends + depends_skip + after_depends).join('')
  end

  if system "stack build --pedantic"
    unused_indices << i
  end
end


puts "found unused:"
unused_indices.map{|i| depends[i]}.each do |x|
  puts x
end

if unused_indices.empty?
  File.open cabal_file, 'w' do |f|
    f.write whole_file
  end
else
  depends_skip = depends.each_with_index.reject{|_,i| unused_indices.include?(i)}.map{|x,_|x}
  File.open cabal_file, 'w' do |f|
    f.write (before_depends + build_depends + depends_skip + after_depends).join('')
  end
end


