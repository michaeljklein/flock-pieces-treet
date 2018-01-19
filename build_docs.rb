#!/usr/bin/env ruby

require 'fileutils'
require 'open3'


stack_haddock_stderr = Open3.capture3('stack haddock')[1]


# Example: ".stack-work/install/x86_64-osx/lts-10.2/8.2.2/doc"
built_docs_dir = stack_haddock_stderr.lines.lazy.map do |x|
  x.chomp.match(/(?<docs_dir>^.*\/\.stack-work\/install\/[^\/]+\/[^\/]+\/[^\/]+\/doc)\/index.html$/)
end.select(&:itself).map do |x|
  x[:docs_dir]
end.first


puts "Stack log:"
puts stack_haddock_stderr
puts
puts "built_docs_dir: #{built_docs_dir}"


# Copy built docs to built_docs_dir
if built_docs_dir && Dir.exist?(built_docs_dir)
  unless File.exist?('.gitignore')
    puts "No .gitignore in current directory, assuming you're not running this right and exiting"
    exit
  end

  system "yes n | cp -r #{built_docs_dir} ."
  puts "Docs copied to doc/"
else
  puts "Unable to find 'built_docs_dir', docs not copied to doc/"
end

