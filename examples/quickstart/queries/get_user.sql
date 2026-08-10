SELECT id, email, display_name
FROM app.users
WHERE id = $1;
